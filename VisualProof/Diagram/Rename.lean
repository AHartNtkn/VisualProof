import VisualProof.Diagram.Boundary

namespace VisualProof.Diagram

open VisualProof.Theory

mutual
  def Region.renameWires (rename : WireRenaming source target) :
      Region source → Region target
    | .mk locals items =>
        .mk locals (items.renameWires (rename.appendRight locals))

  def Item.renameWires (rename : WireRenaming source target) :
      Item source → Item target
    | .atom head ports =>
        .atom (rename head) (ports.map (fun wire => rename wire))
    | .identity signature arity ports =>
        .identity signature arity (fun index => rename (ports index))
    | .cut body => .cut (body.renameWires rename)

  def ItemSeq.renameWires (rename : WireRenaming source target) :
      ItemSeq source → ItemSeq target
    | .nil => .nil
    | .cons head tail =>
        .cons (head.renameWires rename) (tail.renameWires rename)
end

@[simp] theorem vars_map_id (variables : Vars context signatures) :
    variables.map (fun wire => wire) = variables := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons head) induction

theorem vars_map_comp
    (variables : Vars source signatures)
    (first : WireRenaming source middle)
    (second : WireRenaming middle target) :
    (variables.map (fun wire => first wire)).map (fun wire => second wire) =
      variables.map (fun wire => second (first wire)) := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons (second (first head))) induction

private abbrev RegionRenameIdMotive
    (wires : List Sig) (region : Region wires) :=
  region.renameWires WireRenaming.id = region

private abbrev ItemRenameIdMotive
    (wires : List Sig) (item : Item wires) :=
  item.renameWires WireRenaming.id = item

private abbrev ItemsRenameIdMotive
    (wires : List Sig) (items : ItemSeq wires) :=
  items.renameWires WireRenaming.id = items

private def renameIdMkCase
    (locals : List Sig) (items : ItemSeq (outer ++ locals))
    (itemsIH : ItemsRenameIdMotive (outer ++ locals) items) :
    RegionRenameIdMotive outer (.mk locals items) := by
  simp only [RegionRenameIdMotive, Region.renameWires]
  have renameEq :
      (WireRenaming.appendRight WireRenaming.id locals :
        WireRenaming (outer ++ locals) (outer ++ locals)) =
        WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    exact WireRenaming.appendRight_id_apply locals wire
  rw [renameEq, itemsIH]

private def renameIdAtomCase
    (head : Var wires (.rel arguments)) (ports : Vars wires arguments) :
    ItemRenameIdMotive wires (.atom head ports) := by
  simp [ItemRenameIdMotive, Item.renameWires, WireRenaming.id]

private def renameIdIdentityCase
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    ItemRenameIdMotive wires (.identity signature arity ports) := by
  rfl

private def renameIdCutCase
    (body : Region wires) (bodyIH : RegionRenameIdMotive wires body) :
    ItemRenameIdMotive wires (.cut body) :=
  congrArg Item.cut bodyIH

private def renameIdNilCase :
    ItemsRenameIdMotive wires ItemSeq.nil := rfl

private def renameIdConsCase
    (head : Item wires) (tail : ItemSeq wires)
    (headIH : ItemRenameIdMotive wires head)
    (tailIH : ItemsRenameIdMotive wires tail) :
    ItemsRenameIdMotive wires (.cons head tail) := by
  simp only [ItemsRenameIdMotive, ItemSeq.renameWires]
  rw [headIH, tailIH]

theorem Region.renameWires_id (region : Region wires) :
    region.renameWires WireRenaming.id = region :=
  Region.rec renameIdMkCase renameIdAtomCase renameIdIdentityCase
    renameIdCutCase renameIdNilCase renameIdConsCase region

theorem Item.renameWires_id (item : Item wires) :
    item.renameWires WireRenaming.id = item :=
  Item.rec renameIdMkCase renameIdAtomCase renameIdIdentityCase
    renameIdCutCase renameIdNilCase renameIdConsCase item

theorem ItemSeq.renameWires_id (items : ItemSeq wires) :
    items.renameWires WireRenaming.id = items :=
  ItemSeq.rec renameIdMkCase renameIdAtomCase renameIdIdentityCase
    renameIdCutCase renameIdNilCase renameIdConsCase items

private abbrev RegionRenameCompMotive
    (source : List Sig) (region : Region source) :=
  ∀ {middle target : List Sig}
    (first : WireRenaming source middle)
    (second : WireRenaming middle target),
    (region.renameWires first).renameWires second =
      region.renameWires (WireRenaming.comp second first)

private abbrev ItemRenameCompMotive
    (source : List Sig) (item : Item source) :=
  ∀ {middle target : List Sig}
    (first : WireRenaming source middle)
    (second : WireRenaming middle target),
    (item.renameWires first).renameWires second =
      item.renameWires (WireRenaming.comp second first)

private abbrev ItemsRenameCompMotive
    (source : List Sig) (items : ItemSeq source) :=
  ∀ {middle target : List Sig}
    (first : WireRenaming source middle)
    (second : WireRenaming middle target),
    (items.renameWires first).renameWires second =
      items.renameWires (WireRenaming.comp second first)

private def renameCompMkCase
    (locals : List Sig) (items : ItemSeq (source ++ locals))
    (itemsIH : ItemsRenameCompMotive (source ++ locals) items) :
    RegionRenameCompMotive source (.mk locals items) := by
  intro middle target first second
  simp only [Region.renameWires]
  apply congrArg (Region.mk locals)
  calc
    _ = items.renameWires
        (WireRenaming.comp
          (second.appendRight locals) (first.appendRight locals)) :=
      itemsIH _ _
    _ = _ := by
      congr 1
      apply WireRenaming.ext
      intro signature wire
      exact WireRenaming.appendRight_comp_apply first second locals wire

private def renameCompAtomCase
    (head : Var source (.rel arguments)) (ports : Vars source arguments) :
    ItemRenameCompMotive source (.atom head ports) := by
  intro middle target first second
  simp only [Item.renameWires]
  rw [vars_map_comp]
  rfl

private def renameCompIdentityCase
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var source signature) :
    ItemRenameCompMotive source (.identity signature arity ports) := by
  intro middle target first second
  rfl

private def renameCompCutCase
    (body : Region source) (bodyIH : RegionRenameCompMotive source body) :
    ItemRenameCompMotive source (.cut body) := by
  intro middle target first second
  exact congrArg Item.cut (bodyIH first second)

private def renameCompNilCase :
    ItemsRenameCompMotive source ItemSeq.nil := by
  intro middle target first second
  rfl

private def renameCompConsCase
    (head : Item source) (tail : ItemSeq source)
    (headIH : ItemRenameCompMotive source head)
    (tailIH : ItemsRenameCompMotive source tail) :
    ItemsRenameCompMotive source (.cons head tail) := by
  intro middle target first second
  simp only [ItemSeq.renameWires]
  rw [headIH first second, tailIH first second]

theorem Region.renameWires_comp (region : Region source)
    (first : WireRenaming source middle)
    (second : WireRenaming middle target) :
    (region.renameWires first).renameWires second =
      region.renameWires (WireRenaming.comp second first) :=
  Region.rec (motive_1 := RegionRenameCompMotive)
    (motive_2 := ItemRenameCompMotive)
    (motive_3 := ItemsRenameCompMotive)
    renameCompMkCase renameCompAtomCase renameCompIdentityCase
    renameCompCutCase renameCompNilCase renameCompConsCase region first second

theorem Item.renameWires_comp (item : Item source)
    (first : WireRenaming source middle)
    (second : WireRenaming middle target) :
    (item.renameWires first).renameWires second =
      item.renameWires (WireRenaming.comp second first) :=
  Item.rec (motive_1 := RegionRenameCompMotive)
    (motive_2 := ItemRenameCompMotive)
    (motive_3 := ItemsRenameCompMotive)
    renameCompMkCase renameCompAtomCase renameCompIdentityCase
    renameCompCutCase renameCompNilCase renameCompConsCase item first second

theorem ItemSeq.renameWires_comp (items : ItemSeq source)
    (first : WireRenaming source middle)
    (second : WireRenaming middle target) :
    (items.renameWires first).renameWires second =
      items.renameWires (WireRenaming.comp second first) :=
  ItemSeq.rec (motive_1 := RegionRenameCompMotive)
    (motive_2 := ItemRenameCompMotive)
    (motive_3 := ItemsRenameCompMotive)
    renameCompMkCase renameCompAtomCase renameCompIdentityCase
    renameCompCutCase renameCompNilCase renameCompConsCase items first second

end VisualProof.Diagram
