import VisualProof.Diagram.Isomorphism
import VisualProof.Diagram.Rename

namespace VisualProof.Diagram

open VisualProof.Theory

private def Var.dropAppendNil :
    (context : List Sig) → Var (context ++ []) signature → Var context signature
  | [], wire => Fin.elim0 wire.index
  | _ :: _, .here => .here
  | _ :: tail, .there wire => .there (dropAppendNil tail wire)

private theorem Var.dropAppendNil_appendLeft
    (wire : Var context signature) :
    Var.dropAppendNil context (wire.appendLeft []) = wire := by
  induction context with
  | nil => exact Fin.elim0 wire.index
  | cons head tail induction =>
      cases wire with
      | here => rfl
      | there nested => exact congrArg Var.there (induction nested)

/-- The canonical typed equivalence between a context and its append-nil
presentation. -/
def WireEquiv.appendNil (context : List Sig) :
    WireEquiv context (context ++ []) where
  toRenaming := ⟨fun wire => wire.appendLeft []⟩
  invRenaming := ⟨Var.dropAppendNil context⟩
  left_inv := by
    intro signature wire
    exact Var.dropAppendNil_appendLeft wire
  right_inv := by
    intro signature wire
    apply Var.appendCases (left := context) (right := [])
      (motive := fun wire =>
        (Var.dropAppendNil context wire).appendLeft [] = wire)
    · intro signature inherited
      exact congrArg (fun wire => wire.appendLeft [])
        (Var.dropAppendNil_appendLeft inherited)
    · intro signature impossible
      exact Fin.elim0 impossible.index

def FiniteEquiv.succ
    (equivalence : FiniteEquiv (Fin source) (Fin target)) :
    FiniteEquiv (Fin (source + 1)) (Fin (target + 1)) where
  toFun := Fin.cases 0 (fun index => (equivalence index).succ)
  invFun := Fin.cases 0 (fun index => (equivalence.symm index).succ)
  left_inv := by
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · rfl
    · simpa only [Fin.cases_succ] using
        congrArg Fin.succ (equivalence.left_inv tail)
  right_inv := by
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · rfl
    · simpa only [Fin.cases_succ] using
        congrArg Fin.succ (equivalence.right_inv tail)

noncomputable def ItemSeqIso.cons
    (head : ItemIso ambient sourceHead targetHead)
    (tail : ItemSeqIso ambient sourceTail targetTail) :
    ItemSeqIso ambient (.cons sourceHead sourceTail)
      (.cons targetHead targetTail) :=
  match tail with
  | .permute positions items =>
      .permute (FiniteEquiv.succ positions) fun sourceIndex targetIndex equal => by
        refine Fin.cases (motive := fun sourceIndex =>
          FiniteEquiv.succ positions sourceIndex = targetIndex →
            ItemIso ambient
              ((ItemSeq.cons sourceHead sourceTail).get sourceIndex)
              ((ItemSeq.cons targetHead targetTail).get targetIndex)) ?_ ?_
          sourceIndex equal
        · intro equal
          refine Fin.cases (motive := fun targetIndex =>
            FiniteEquiv.succ positions 0 = targetIndex →
              ItemIso ambient sourceHead
                ((ItemSeq.cons targetHead targetTail).get targetIndex)) ?_ ?_
            targetIndex equal
          · intro _
            exact head
          · intro targetTailIndex impossible
            exact False.elim (by
              have values := congrArg Fin.val impossible
              simp [FiniteEquiv.succ] at values)
        · intro sourceTailIndex equal
          refine Fin.cases (motive := fun targetIndex =>
            FiniteEquiv.succ positions sourceTailIndex.succ = targetIndex →
              ItemIso ambient (sourceTail.get sourceTailIndex)
                ((ItemSeq.cons targetHead targetTail).get targetIndex)) ?_ ?_
            targetIndex equal
          · intro impossible
            exact False.elim (by
              have values := congrArg Fin.val impossible
              simp [FiniteEquiv.succ] at values)
          · intro targetTailIndex equal
            apply items sourceTailIndex targetTailIndex
            apply Fin.ext
            have values := congrArg Fin.val equal
            simpa [FiniteEquiv.succ] using Nat.succ.inj values

private abbrev RenameRegionIsoMotive
    (source target : List Sig) (equivalence : WireEquiv source target)
    (region : Region source) :=
  RegionIso equivalence region
    (region.renameWires equivalence.toRenaming)

private abbrev RenameItemIsoMotive
    (source target : List Sig) (equivalence : WireEquiv source target)
    (item : Item source) :=
  ItemIso equivalence item (item.renameWires equivalence.toRenaming)

private abbrev RenameItemsIsoMotive
    (source target : List Sig) (equivalence : WireEquiv source target)
    (items : ItemSeq source) :=
  ItemSeqIso equivalence items (items.renameWires equivalence.toRenaming)

private noncomputable def renameRegionIsoMk
    (locals : List Sig) (items : ItemSeq (source ++ locals))
    (itemsIH : ∀ {target : List Sig}
      (equivalence : WireEquiv (source ++ locals) target),
      RenameItemsIsoMotive (source ++ locals) target equivalence items) :
    ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameRegionIsoMotive source target equivalence (.mk locals items) := by
  intro target equivalence
  exact .mk (WireEquiv.refl locals)
    (itemsIH (equivalence.append (WireEquiv.refl locals)))

private noncomputable def renameItemIsoAtom
    (head : Var source (.rel arguments)) (ports : Vars source arguments) :
    ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameItemIsoMotive source target equivalence (.atom head ports) := by
  intro target equivalence
  exact .atom rfl rfl

private noncomputable def renameItemIsoIdentity
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var source signature) :
    ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameItemIsoMotive source target equivalence
        (.identity signature arity ports) := by
  intro target equivalence
  exact .identity rfl

private noncomputable def renameItemIsoCut
    (body : Region source)
    (bodyIH : ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameRegionIsoMotive source target equivalence body) :
    ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameItemIsoMotive source target equivalence (.cut body) := by
  intro target equivalence
  exact .cut (bodyIH equivalence)

private noncomputable def renameItemsIsoNil :
    ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameItemsIsoMotive source target equivalence .nil := by
  intro target equivalence
  exact .permute (FiniteEquiv.refl _) fun index => Fin.elim0 index

private noncomputable def renameItemsIsoCons
    (head : Item source) (tail : ItemSeq source)
    (headIH : ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameItemIsoMotive source target equivalence head)
    (tailIH : ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameItemsIsoMotive source target equivalence tail) :
    ∀ {target : List Sig} (equivalence : WireEquiv source target),
      RenameItemsIsoMotive source target equivalence (.cons head tail) := by
  intro target equivalence
  exact ItemSeqIso.cons (headIH equivalence) (tailIH equivalence)

noncomputable def RegionIso.renameWiresEquiv
    (equivalence : WireEquiv source target) (region : Region source) :
    RegionIso equivalence region
      (region.renameWires equivalence.toRenaming) :=
  Region.rec
    (motive_1 := fun source region => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameRegionIsoMotive source target equivalence region)
    (motive_2 := fun source item => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameItemIsoMotive source target equivalence item)
    (motive_3 := fun source items => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameItemsIsoMotive source target equivalence items)
    renameRegionIsoMk renameItemIsoAtom renameItemIsoIdentity
    renameItemIsoCut renameItemsIsoNil renameItemsIsoCons region equivalence

noncomputable def ItemIso.renameWiresEquiv
    (equivalence : WireEquiv source target) (item : Item source) :
    ItemIso equivalence item (item.renameWires equivalence.toRenaming) :=
  Item.rec
    (motive_1 := fun source region => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameRegionIsoMotive source target equivalence region)
    (motive_2 := fun source item => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameItemIsoMotive source target equivalence item)
    (motive_3 := fun source items => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameItemsIsoMotive source target equivalence items)
    renameRegionIsoMk renameItemIsoAtom renameItemIsoIdentity
    renameItemIsoCut renameItemsIsoNil renameItemsIsoCons item equivalence

noncomputable def ItemSeqIso.renameWiresEquiv
    (equivalence : WireEquiv source target) (items : ItemSeq source) :
    ItemSeqIso equivalence items (items.renameWires equivalence.toRenaming) :=
  ItemSeq.rec
    (motive_1 := fun source region => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameRegionIsoMotive source target equivalence region)
    (motive_2 := fun source item => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameItemIsoMotive source target equivalence item)
    (motive_3 := fun source items => ∀ {target}
      (equivalence : WireEquiv source target),
      RenameItemsIsoMotive source target equivalence items)
    renameRegionIsoMk renameItemIsoAtom renameItemIsoIdentity
    renameItemIsoCut renameItemsIsoNil renameItemsIsoCons items equivalence

end VisualProof.Diagram
