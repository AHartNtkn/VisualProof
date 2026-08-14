import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

open VisualProof.Theory

namespace Region

def blank (outer : List Sig) : Region outer := .mk [] .nil

/-- Embed the first conjunct's wires into the combined local context. -/
def conjoinLeftWire (outer firstLocals secondLocals : List Sig) :
    WireRenaming (outer ++ firstLocals)
      (outer ++ (firstLocals ++ secondLocals)) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (firstLocals ++ secondLocals))
    (fun wire => Var.appendRight outer (wire.appendLeft secondLocals))⟩

/-- Embed the second conjunct's wires into the combined local context. -/
def conjoinRightWire (outer firstLocals secondLocals : List Sig) :
    WireRenaming (outer ++ secondLocals)
      (outer ++ (firstLocals ++ secondLocals)) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (firstLocals ++ secondLocals))
    (fun wire => Var.appendRight outer
      (Var.appendRight firstLocals wire))⟩

/-- Intrinsic conjunction with disjoint ownership of each operand's locals. -/
def conjoin : Region outer → Region outer → Region outer
  | .mk firstLocals firstItems, .mk secondLocals secondItems =>
      .mk (firstLocals ++ secondLocals)
        ((firstItems.renameWires
            (conjoinLeftWire outer firstLocals secondLocals)).append
          (secondItems.renameWires
            (conjoinRightWire outer firstLocals secondLocals)))

/-- Embed existing host wires when adjoining new locals after them. -/
def adjoinHostWire (outer hostLocals addedLocals : List Sig) :
    WireRenaming (outer ++ hostLocals)
      (outer ++ (hostLocals ++ addedLocals)) :=
  conjoinLeftWire outer hostLocals addedLocals

/-- Reassociate the material's inherited host context and new locals. -/
def adjoinMaterialWire (outer hostLocals addedLocals : List Sig) :
    WireRenaming ((outer ++ hostLocals) ++ addedLocals)
      (outer ++ (hostLocals ++ addedLocals)) :=
  ⟨Var.appendMap
    (Var.appendMap
      (fun wire => wire.appendLeft (hostLocals ++ addedLocals))
      (fun wire => Var.appendRight outer (wire.appendLeft addedLocals)))
    (fun wire => Var.appendRight outer (Var.appendRight hostLocals wire))⟩

/-- Adjoin material after a region's existing items and local wires. -/
def adjoinAt (hostLocals : List Sig)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) : Region outer :=
  match material with
  | .mk addedLocals addedItems =>
      .mk (hostLocals ++ addedLocals)
        ((hostItems.renameWires
            (adjoinHostWire outer hostLocals addedLocals)).append
          (addedItems.renameWires
            (adjoinMaterialWire outer hostLocals addedLocals)))

/-- Capture-avoiding insertion of recursively typed material. -/
def spliceAt (hostLocals : List Sig)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region patternWires)
    (wireMap : WireRenaming patternWires (outer ++ hostLocals)) :
    Region outer :=
  adjoinAt hostLocals hostItems (material.renameWires wireMap)

end Region

structure ItemSeq.Focus (items : ItemSeq wires) where
  before : ItemSeq wires
  item : Item wires
  after : ItemSeq wires
  rebuild : before.append (.cons item after) = items

end VisualProof.Diagram
