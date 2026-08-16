import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

open VisualProof.Theory

namespace Region

def blank (outer : List Sig) : Region outer := .mk [] .nil

/-- One item sequence as an independently conjoinable zero-local region. -/
def ofItems (items : ItemSeq outer) : Region outer :=
  let appendNil : WireRenaming outer (outer ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  .mk [] (items.renameWires appendNil)

/-- One item as an independently conjoinable zero-local region. -/
def singleton (item : Item outer) : Region outer :=
  ofItems (ItemSeq.cons item ItemSeq.nil)

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

def ItemSeq.focusAt : (items : ItemSeq wires) →
    Fin items.length → ItemSeq.Focus items
  | .nil, index => Fin.elim0 index
  | .cons head tail, index => Fin.cases {
      before := .nil
      item := head
      after := tail
      rebuild := rfl
    } (fun tailIndex =>
      let nested := tail.focusAt tailIndex
      {
        before := .cons head nested.before
        item := nested.item
        after := nested.after
        rebuild := by
          simp only [ItemSeq.append]
          rw [nested.rebuild]
      }) index

@[simp] theorem ItemSeq.length_append
    (first second : ItemSeq wires) :
    (first.append second).length = first.length + second.length :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun _ first => ∀ second,
      (first.append second).length = first.length + second.length)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun second => by simp [ItemSeq.append, ItemSeq.length])
    (fun _ _ _ induction second => by
      simp only [ItemSeq.append, ItemSeq.length]
      rw [induction second]
      omega)
    first second

theorem ItemSeq.focusAt_item_eq_get
    (items : ItemSeq wires) (index : Fin items.length) :
    (items.focusAt index).item = items.get index :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun _ items => ∀ index : Fin items.length,
      (items.focusAt index).item = items.get index)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun index => Fin.elim0 index)
    (fun _ _ _ induction index => Fin.cases rfl induction index)
    items index

end VisualProof.Diagram
