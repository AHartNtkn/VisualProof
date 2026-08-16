import VisualProof.Diagram.IdentityOccurrence
import VisualProof.Diagram.Isomorphism.Rename

namespace VisualProof.Diagram

open VisualProof.Theory

namespace FiniteEquiv
private def swapFirstTwo (tailLength : Nat) :
    FiniteEquiv (Fin (tailLength + 2)) (Fin (tailLength + 2)) where
  toFun := Fin.cases 1
    (fun index => Fin.cases 0 (fun rest => Fin.succ (Fin.succ rest)) index)
  invFun := Fin.cases 1
    (fun index => Fin.cases 0 (fun rest => Fin.succ (Fin.succ rest)) index)
  left_inv := by
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · rfl
    · refine Fin.cases ?_ (fun rest => ?_) tail
      · rfl
      · rfl
  right_inv := by
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · rfl
    · refine Fin.cases ?_ (fun rest => ?_) tail
      · rfl
      · rfl

end FiniteEquiv

namespace ItemSeqIso

private noncomputable def swapFirstTwo
    (first second : Item wires) (tail : ItemSeq wires) :
    ItemSeqIso (WireEquiv.refl wires)
      (.cons first (.cons second tail))
      (.cons second (.cons first tail)) :=
  .permute (FiniteEquiv.swapFirstTwo tail.length)
    fun sourceIndex targetIndex equal => by
      refine Fin.cases (motive := fun index =>
        FiniteEquiv.swapFirstTwo tail.length index = targetIndex →
          ItemIso (WireEquiv.refl wires)
            ((ItemSeq.cons first (ItemSeq.cons second tail)).get index)
            ((ItemSeq.cons second (ItemSeq.cons first tail)).get targetIndex)) ?_ ?_
        sourceIndex equal
      · intro equal
        refine Fin.cases (motive := fun targetIndex =>
          FiniteEquiv.swapFirstTwo tail.length 0 = targetIndex →
            ItemIso (WireEquiv.refl wires) first
              ((ItemSeq.cons second (ItemSeq.cons first tail)).get targetIndex)) ?_ ?_
          targetIndex equal
        · intro impossible
          exact False.elim (by
            have values := congrArg Fin.val impossible
            simp [FiniteEquiv.swapFirstTwo] at values)
        · intro targetTailIndex equal
          refine Fin.cases (motive := fun targetTailIndex =>
            FiniteEquiv.swapFirstTwo tail.length 0 = targetTailIndex.succ →
              ItemIso (WireEquiv.refl wires) first
                ((ItemSeq.cons first tail).get targetTailIndex)) ?_ ?_
            targetTailIndex equal
          · intro _
            exact ItemIso.refl first
          · intro rest impossible
            exact False.elim (by
              have values := congrArg Fin.val impossible
              simp [FiniteEquiv.swapFirstTwo] at values)
      · intro sourceTail equal
        refine Fin.cases (motive := fun index =>
          FiniteEquiv.swapFirstTwo tail.length index.succ = targetIndex →
            ItemIso (WireEquiv.refl wires)
              ((ItemSeq.cons first (ItemSeq.cons second tail)).get index.succ)
              ((ItemSeq.cons second (ItemSeq.cons first tail)).get targetIndex)) ?_ ?_
          sourceTail equal
        · intro equal
          refine Fin.cases (motive := fun targetIndex =>
            FiniteEquiv.swapFirstTwo tail.length 1 = targetIndex →
              ItemIso (WireEquiv.refl wires) second
                ((ItemSeq.cons second (ItemSeq.cons first tail)).get targetIndex)) ?_ ?_
            targetIndex equal
          · intro _
            exact ItemIso.refl second
          · intro targetTail impossible
            exact False.elim (by
              have values := congrArg Fin.val impossible
              change 0 = targetTail.val + 1 at values
              omega)
        · intro rest equal
          refine Fin.cases (motive := fun targetIndex =>
            FiniteEquiv.swapFirstTwo tail.length rest.succ.succ = targetIndex →
              ItemIso (WireEquiv.refl wires) (tail.get rest)
                ((ItemSeq.cons second (ItemSeq.cons first tail)).get targetIndex)) ?_ ?_
            targetIndex equal
          · intro impossible
            exact False.elim (by
              have values := congrArg Fin.val impossible
              simp [FiniteEquiv.swapFirstTwo] at values)
          · intro targetTail equal
            refine Fin.cases (motive := fun targetTail =>
              FiniteEquiv.swapFirstTwo tail.length rest.succ.succ = targetTail.succ →
                ItemIso (WireEquiv.refl wires) (tail.get rest)
                  ((ItemSeq.cons first tail).get targetTail)) ?_ ?_
              targetTail equal
            · intro impossible
              exact False.elim (by
                have values := congrArg Fin.val impossible
                simp [FiniteEquiv.swapFirstTwo] at values)
            · intro targetRest equal
              have rest_eq : rest = targetRest := by
                apply Fin.ext
                have values := congrArg Fin.val equal
                simpa [FiniteEquiv.swapFirstTwo] using
                  Nat.succ.inj (Nat.succ.inj values)
              subst targetRest
              exact ItemIso.refl (tail.get rest)

private theorem refl_trans_refl (wires : List Sig) :
    (WireEquiv.refl wires).trans (WireEquiv.refl wires) =
      WireEquiv.refl wires := by
  apply WireEquiv.ext
  intro signature wire
  rfl

private noncomputable def moveToFront
    (before : ItemSeq wires) (selected : Item wires)
    (after : ItemSeq wires) :
    ItemSeqIso (WireEquiv.refl wires)
      (before.append (.cons selected after))
      (.cons selected (before.append after)) :=
  match before with
  | .nil => ItemSeqIso.refl _
  | .cons head tail =>
      let movedTail := moveToFront tail selected after
      let keptHead := ItemSeqIso.cons (ItemIso.refl head) movedTail
      (keptHead.trans
        (swapFirstTwo head selected (tail.append after))).castAmbient
          (refl_trans_refl wires)

noncomputable def prependRefl
    (initial : ItemSeq wires)
    (suffix : ItemSeqIso (WireEquiv.refl wires) source target) :
    ItemSeqIso (WireEquiv.refl wires)
      (initial.append source) (initial.append target) :=
  match initial with
  | .nil => suffix
  | .cons head tail =>
      ItemSeqIso.cons (ItemIso.refl head) (prependRefl tail suffix)

end ItemSeqIso

namespace ItemSeq
namespace Focus

noncomputable def frontIso
    {wires : List Sig} {items : ItemSeq wires}
    (focus : _root_.VisualProof.Diagram.ItemSeq.Focus items) :
    ItemSeqIso (WireEquiv.refl wires) items
      (.cons focus.item (focus.before.append focus.after)) := by
  cases focus with
  | mk before selected after rebuild =>
      subst items
      exact ItemSeqIso.moveToFront before selected after

noncomputable def regionFrontIso
    {outer locals : List Sig} {items : ItemSeq (outer ++ locals)}
    (focus : _root_.VisualProof.Diagram.ItemSeq.Focus items) :
    RegionIso (WireEquiv.refl outer) (.mk locals items)
      (.mk locals (.cons focus.item (focus.before.append focus.after))) :=
  .mk (WireEquiv.refl locals)
    (focus.frontIso.castAmbient (WireEquiv.append_refl outer locals).symm)

end Focus
end ItemSeq

noncomputable def DiagramContext.fillIso
    (context : DiagramContext outer holeWires)
    (body : RegionIso (WireEquiv.refl holeWires) source target) :
    RegionIso (WireEquiv.refl outer)
      (context.fill source) (context.fill target) := by
  induction context with
  | hole => exact body
  | cut locals before after child ih =>
      let childIso := ih body
      let tailIso := ItemSeqIso.cons (.cut childIso) (ItemSeqIso.refl after)
      let itemsIso := ItemSeqIso.prependRefl before tailIso
      exact .mk (WireEquiv.refl locals)
        (itemsIso.castAmbient (WireEquiv.append_refl _ locals).symm)

/-- Present one focused item as an independently selected zero-local block,
with every other item retained as the remainder at the same region. -/
def Region.focusedAt {outer : List Sig} (locals : List Sig)
    {items : ItemSeq (outer ++ locals)}
    (focus : ItemSeq.Focus items) : Region outer :=
  Region.adjoinAt locals .nil
    ((Region.singleton focus.item).conjoin
      (Region.ofItems (focus.before.append focus.after)))

theorem Region.focusedAt_eq
    {outer locals : List Sig} {items : ItemSeq (outer ++ locals)}
    (focus : ItemSeq.Focus items) :
    let equivalence :=
      (WireEquiv.refl outer).append (WireEquiv.appendNil locals)
    Region.focusedAt locals focus =
      Region.mk (locals ++ [])
        ((ItemSeq.cons focus.item (focus.before.append focus.after)).renameWires
          equivalence.toRenaming) := by
  simp only [Region.focusedAt, Region.adjoinAt, Region.conjoin,
    Region.singleton, Region.ofItems, ItemSeq.renameWires,
    ItemSeq.nil_append, ItemSeq.append, Item.renameWires_comp,
    ItemSeq.renameWires_comp]
  apply congrArg (Region.mk (locals ++ []))
  congr 1
  · apply congrArg (fun rename => focus.item.renameWires rename)
      (WireRenaming.ext _ _ ?_)
    intro signature wire
    apply Var.appendCases (left := outer) (right := locals)
      (motive := fun wire =>
        (WireRenaming.comp (Region.adjoinMaterialWire outer locals [])
          (WireRenaming.comp (Region.conjoinLeftWire (outer ++ locals) [] [])
            ⟨fun wire => wire.appendLeft []⟩)) wire =
          ((WireEquiv.refl outer).append (WireEquiv.appendNil locals)) wire)
    · intro signature inherited
      simp [Region.adjoinMaterialWire, Region.conjoinLeftWire,
        WireRenaming.comp, WireEquiv.append_apply_left, WireEquiv.appendNil]
    · intro signature localWire
      simp [Region.adjoinMaterialWire, Region.conjoinLeftWire,
        WireRenaming.comp, WireEquiv.append_apply_right, WireEquiv.appendNil]
  · apply congrArg (fun rename =>
        (focus.before.append focus.after).renameWires rename)
      (WireRenaming.ext _ _ ?_)
    intro signature wire
    apply Var.appendCases (left := outer) (right := locals)
      (motive := fun wire =>
        (WireRenaming.comp (Region.adjoinMaterialWire outer locals [])
          (WireRenaming.comp (Region.conjoinRightWire (outer ++ locals) [] [])
            ⟨fun wire => wire.appendLeft []⟩)) wire =
          ((WireEquiv.refl outer).append (WireEquiv.appendNil locals)) wire)
    · intro signature inherited
      simp [Region.adjoinMaterialWire, Region.conjoinRightWire,
        WireRenaming.comp, WireEquiv.append_apply_left, WireEquiv.appendNil]
    · intro signature localWire
      simp [Region.adjoinMaterialWire, Region.conjoinRightWire,
        WireRenaming.comp, WireEquiv.append_apply_right, WireEquiv.appendNil]

noncomputable def ItemSeq.Focus.regionIso
    {outer locals : List Sig} {items : ItemSeq (outer ++ locals)}
    (focus : ItemSeq.Focus items) :
    RegionIso (WireEquiv.refl outer) (.mk locals items)
      (Region.focusedAt locals focus) := by
  rw [Region.focusedAt_eq focus]
  let equivalence :=
    (WireEquiv.refl outer).append (WireEquiv.appendNil locals)
  let moved := focus.frontIso
  let renamed := ItemSeqIso.cons
    (ItemIso.renameWiresEquiv equivalence focus.item)
    (ItemSeqIso.renameWiresEquiv equivalence
      (focus.before.append focus.after))
  exact .mk (WireEquiv.appendNil locals)
    ((moved.trans renamed).castAmbient (by
      apply WireEquiv.ext
      intro signature wire
      rfl))

end VisualProof.Diagram
