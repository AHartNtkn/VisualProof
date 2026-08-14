import VisualProof.Diagram.Rename

namespace VisualProof.Diagram

open VisualProof.Theory

/-- A recursive one-hole diagram context. Relation quantification is carried by
typed regional wires, so the only enclosing item frame is a cut. -/
inductive DiagramContext : (outer hole : List Sig) → Type
  | hole : DiagramContext wires wires
  | cut (locals : List Sig)
      (before after : ItemSeq (outer ++ locals))
      (child : DiagramContext (outer ++ locals) hole) :
      DiagramContext outer hole

inductive Polarity
  | positive
  | negative

namespace DiagramContext

def cutDepth : DiagramContext outer holeWires → Nat
  | .hole => 0
  | .cut _ _ _ child => child.cutDepth + 1

def polarity (context : DiagramContext outer holeWires) : Polarity :=
  if context.cutDepth % 2 = 0 then .positive else .negative

def fill : DiagramContext outer holeWires → Region holeWires → Region outer
  | .hole, body => body
  | .cut locals before after child, body =>
      .mk locals (before.append (.cons (.cut (child.fill body)) after))

/-- Compose nested one-hole contexts without introducing a second path. -/
def comp (outer : DiagramContext outside middle)
    (inner : DiagramContext middle holeWires) :
    DiagramContext outside holeWires :=
  match outer with
  | .hole => inner
  | .cut locals before after child =>
      .cut locals before after (child.comp inner)

@[simp] theorem fill_comp
    (outer : DiagramContext outside middle)
    (inner : DiagramContext middle holeWires)
    (body : Region holeWires) :
    (outer.comp inner).fill body = outer.fill (inner.fill body) := by
  induction outer with
  | hole => rfl
  | cut locals before after child induction =>
      simp only [comp, fill, induction]

/-- Embed wires inherited outside a context into the interface at its hole. -/
def outerWire : DiagramContext outer holeWires →
    WireRenaming outer holeWires
  | .hole => WireRenaming.id
  | .cut locals _ _ child =>
      WireRenaming.comp child.outerWire
        ⟨fun wire => wire.appendLeft locals⟩

end DiagramContext

end VisualProof.Diagram
