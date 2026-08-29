import VisualProof.Diagram.Rename

namespace VisualProof.Diagram

open VisualProof.Theory

namespace ItemSeq

/-- Emit unary identities for a decidable selection of typed wires. -/
def pinWires :
    (source : List Sig) →
    WireRenaming source target →
    (∀ {signature}, Var source signature → Bool) →
    ItemSeq target
  | [], _, _ => .nil
  | _ :: rest, renameWires, selected =>
      let tailRename : WireRenaming rest target :=
        ⟨fun wire => renameWires (.there wire)⟩
      let tailSelected : ∀ {signature}, Var rest signature → Bool :=
        fun wire => selected (.there wire)
      let tail := pinWires rest tailRename tailSelected
      if selected (.here) then
        .cons (.identity _ 1 (fun _ => renameWires (.here))) tail
      else tail

theorem pinWires_renameWires
    (source : List Sig) (rename : WireRenaming source middle)
    (next : WireRenaming middle target)
    (selected : ∀ {signature}, Var source signature → Bool) :
    (pinWires source rename selected).renameWires next =
      pinWires source (WireRenaming.comp next rename) selected := by
  induction source with
  | nil => rfl
  | cons signature tail induction =>
      simp only [pinWires]
      split
      · simp only [ItemSeq.renameWires, Item.renameWires]
        exact congrArg (ItemSeq.cons
          (.identity signature 1
            (fun _ => next (rename (.here : Var (signature :: tail)
              signature)))))
          (induction ⟨fun wire => rename (.there wire)⟩
            (fun wire => selected (.there wire)))
      · exact induction ⟨fun wire => rename (.there wire)⟩
          (fun wire => selected (.there wire))

/-- Whether one wire has any incidence in an item sequence. -/
def usesWire (items : ItemSeq wires) (wire : Var wires signature) : Bool :=
  decide (items.incidencePaths wire.index.val 0 ≠ [])

/-- Whether a wire needs a direct unary identity for this item sequence to
give it at least two incidences at the current region root. -/
def needsRootPin (items : ItemSeq wires)
    (wire : Var wires signature) : Bool :=
  let paths := items.incidencePaths wire.index.val 0
  decide (¬RegionPath.RootedTwo paths)

/-- Directly complete selected wires against their actual incidence paths.
The first batch emits one unary pin for every wire that is not already
`RootedTwo`; the second emits the distinct additional pin needed only when
there are no existing incidences. -/
def rootedTwoPins
    (source : List Sig) (renameWires : WireRenaming source target)
    (paths : ∀ {signature}, Var source signature → List RegionPath) :
    ItemSeq target :=
  let primary := pinWires source renameWires
    (fun wire => decide (¬RegionPath.RootedTwo (paths wire)))
  let extra := pinWires source renameWires
    (fun wire => decide (paths wire = []))
  primary.append extra

theorem pinWires_childrenCanonical
    (source : List Sig) (renameWires : WireRenaming source target)
    (selected : ∀ {signature}, Var source signature → Bool) :
    (pinWires source renameWires selected).ChildrenCanonical := by
  induction source with
  | nil => trivial
  | cons signature rest induction =>
      simp only [pinWires]
      split
      · exact ⟨True.intro,
          induction
            ⟨fun wire => renameWires (.there wire)⟩
            (fun wire => selected (.there wire))⟩
      · exact induction
          ⟨fun wire => renameWires (.there wire)⟩
          (fun wire => selected (.there wire))

theorem rootedTwoPins_childrenCanonical
    (source : List Sig) (renameWires : WireRenaming source target)
    (paths : ∀ {signature}, Var source signature → List RegionPath) :
    (rootedTwoPins source renameWires paths).ChildrenCanonical := by
  apply (ItemSeq.childrenCanonical_append _ _).mpr
  exact ⟨pinWires_childrenCanonical _ _ _,
    pinWires_childrenCanonical _ _ _⟩

theorem pinWires_mem_nil
    (source : List Sig) (renameWires : WireRenaming source target)
    (selected : ∀ {signature}, Var source signature → Bool)
    (wire : Var source signature) (itemIndex : Nat)
    (selectedWire : selected wire = true) :
    [] ∈ (pinWires source renameWires selected).incidencePaths
      (renameWires wire).index.val itemIndex := by
  induction source generalizing target signature itemIndex with
  | nil => exact nomatch wire
  | cons head rest induction =>
      cases wire with
      | here =>
          simp [pinWires, selectedWire, ItemSeq.incidencePaths,
            Item.incidencePaths]
      | @there _ _ _ tailWire =>
          simp only [pinWires]
          cases selectedHead : selected (.here) with
          | true =>
            simp only [if_true, ItemSeq.incidencePaths,
              List.mem_append]
            exact Or.inr (induction
              ⟨fun wire => renameWires (.there wire)⟩
              (fun wire => selected (.there wire)) tailWire
              (itemIndex + 1) selectedWire)
          | false =>
            simp only [Bool.false_eq]
            exact induction
              ⟨fun wire => renameWires (.there wire)⟩
              (fun wire => selected (.there wire)) tailWire
              itemIndex selectedWire

theorem pinWires_incidence_eq_nil_of
    (source : List Sig) (renameWires : WireRenaming source target)
    (selected : ∀ {signature}, Var source signature → Bool)
    (wireIndex itemIndex : Nat)
    (noneAt : ∀ {signature} (wire : Var source signature),
      selected wire = true → (renameWires wire).index.val ≠ wireIndex) :
    (pinWires source renameWires selected).incidencePaths
      wireIndex itemIndex = [] := by
  induction source generalizing target itemIndex with
  | nil => rfl
  | cons head rest induction =>
      simp only [pinWires]
      cases selectedHead : selected (.here) with
      | false =>
          simp only [Bool.false_eq]
          exact induction
            ⟨fun wire => renameWires (.there wire)⟩
            (fun wire => selected (.there wire)) itemIndex
            (by
              intro signature wire selectedWire
              exact noneAt (.there wire) selectedWire)
      | true =>
          simp only [if_true, ItemSeq.incidencePaths, Item.incidencePaths]
          have headNe := noneAt (.here) selectedHead
          have headCount :
              (List.ofFn fun _ : Fin 1 => (renameWires (.here)).index.val).count
                wireIndex = 0 := by
            simp [headNe]
          rw [headCount]
          simp only [List.replicate_zero, List.nil_append]
          exact induction
            ⟨fun wire => renameWires (.there wire)⟩
            (fun wire => selected (.there wire)) (itemIndex + 1)
            (by
              intro signature wire selectedWire
              exact noneAt (.there wire) selectedWire)

end ItemSeq

end VisualProof.Diagram
