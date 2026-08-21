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

@[simp] theorem conjoinLeftWire_index_val
    (wire : Var (outer ++ firstLocals) signature) :
    (conjoinLeftWire outer firstLocals secondLocals wire).index.val =
      wire.index.val := by
  apply Var.appendCases (left := outer) (right := firstLocals)
    (motive := fun wire =>
      (conjoinLeftWire outer firstLocals secondLocals wire).index.val =
        wire.index.val)
  · intro inheritedSignature inherited
    simp [conjoinLeftWire]
  · intro localSignature localWire
    simp [conjoinLeftWire]

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

theorem ofItems_conjoin (first second : ItemSeq outer) :
    (ofItems first).conjoin (ofItems second) =
      ofItems (first.append second) := by
  let appendNil : WireRenaming outer (outer ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  have leftMap : WireRenaming.comp
      (conjoinLeftWire outer [] []) appendNil = appendNil := by
    apply WireRenaming.ext
    intro signature wire
    simp [WireRenaming.comp, conjoinLeftWire, appendNil]
  have rightMap : WireRenaming.comp
      (conjoinRightWire outer [] []) appendNil = appendNil := by
    apply WireRenaming.ext
    intro signature wire
    simp [WireRenaming.comp, conjoinRightWire, appendNil]
  simp only [ofItems, conjoin, ItemSeq.renameWires_append,
    ItemSeq.renameWires_comp]
  rw [leftMap, rightMap]
  rfl

/-- Embed existing host wires when adjoining new locals after them. -/
def adjoinHostWire (outer hostLocals addedLocals : List Sig) :
    WireRenaming (outer ++ hostLocals)
      (outer ++ (hostLocals ++ addedLocals)) :=
  conjoinLeftWire outer hostLocals addedLocals

@[simp] theorem adjoinHostWire_index_val
    (wire : Var (outer ++ hostLocals) signature) :
    (adjoinHostWire outer hostLocals addedLocals wire).index.val =
      wire.index.val :=
  conjoinLeftWire_index_val wire

/-- Reassociate the material's inherited host context and new locals. -/
def adjoinMaterialWire (outer hostLocals addedLocals : List Sig) :
    WireRenaming ((outer ++ hostLocals) ++ addedLocals)
      (outer ++ (hostLocals ++ addedLocals)) :=
  ⟨Var.appendMap
    (Var.appendMap
      (fun wire => wire.appendLeft (hostLocals ++ addedLocals))
      (fun wire => Var.appendRight outer (wire.appendLeft addedLocals)))
    (fun wire => Var.appendRight outer (Var.appendRight hostLocals wire))⟩

@[simp] theorem adjoinMaterialWire_index_val
    (wire : Var ((outer ++ hostLocals) ++ addedLocals) signature) :
    (adjoinMaterialWire outer hostLocals addedLocals wire).index.val =
      wire.index.val := by
  apply Var.appendCases (left := outer ++ hostLocals)
    (right := addedLocals)
    (motive := fun wire =>
      (adjoinMaterialWire outer hostLocals addedLocals wire).index.val =
        wire.index.val)
  · intro inheritedSignature inherited
    apply Var.appendCases (left := outer) (right := hostLocals)
      (motive := fun inherited =>
        (adjoinMaterialWire outer hostLocals addedLocals
          (inherited.appendLeft addedLocals)).index.val =
            (inherited.appendLeft addedLocals).index.val)
    · intro outerSignature outerWire
      simp [adjoinMaterialWire]
    · intro hostSignature hostWire
      simp [adjoinMaterialWire]
  · intro localSignature localWire
    simp [adjoinMaterialWire]
    omega

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
