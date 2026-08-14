import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

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

private def retainedItems
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires) :
    ItemSeq (outer ++ (hostLocals ++ material.locals)) :=
  match material with
  | .mk addedLocals _ =>
      hostItems.renameWires
        (Region.adjoinHostWire outer hostLocals addedLocals)

private def removedItems
    (hostLocals : List Sig) (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals)) :
    ItemSeq (outer ++ (hostLocals ++ material.locals)) :=
  match material with
  | .mk addedLocals addedItems =>
      addedItems.renameWires
        (WireRenaming.comp
          (Region.adjoinMaterialWire outer hostLocals addedLocals)
          (wireMap.appendRight addedLocals))

private def pinNeeded
    (retained : ItemSeq (outer ++ locals))
    (wire : Var locals signature) : Bool :=
  let paths := retained.incidencePaths
    (outer.length + wire.index.val) 0
  decide (¬(paths ≠ [] ∧ RegionPath.deepestCommonAncestor paths = []))

private def removedUsed (removed : ItemSeq wires)
    (wire : Var wires signature) : Bool :=
  decide (removed.incidencePaths wire.index.val 0 ≠ [])

/-- Canonical ownership residue left after material is erased. It retains every
locally quantified wire and adds a unary identity exactly when the retained
items no longer place that wire at this region's DCA. -/
def residue
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals)) :
    ItemSeq (outer ++ (hostLocals ++ material.locals)) :=
  let retained := retainedItems hostLocals hostItems material
  let removed := removedItems hostLocals material wireMap
  let removedPins := pinWires (outer ++ (hostLocals ++ material.locals))
    WireRenaming.id (removedUsed removed)
  let localPins := pinWires (hostLocals ++ material.locals)
    ⟨fun wire => Var.appendRight outer wire⟩ (pinNeeded retained)
  removedPins.append localPins

/-- Erasure preserves the quantified wire owners and replaces any ownership
support lost with unary identities. -/
def eraseAt
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals)) :
    Region outer :=
  .mk (hostLocals ++ material.locals)
    ((retainedItems hostLocals hostItems material).append
      (residue hostLocals hostItems material wireMap))

private theorem pinWires_childrenCanonical
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

private theorem pinWires_mem_nil
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

theorem eraseAt_canonical
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires) (wireMap : WireRenaming materialWires
      (outer ++ hostLocals))
    (sourceCanonical :
      (Region.spliceAt hostLocals hostItems material wireMap).Canonical) :
    (eraseAt hostLocals hostItems material wireMap).Canonical := by
  cases material with
  | mk addedLocals addedItems =>
      let retained := hostItems.renameWires
        (Region.adjoinHostWire outer hostLocals addedLocals)
      let pins := pinWires (hostLocals ++ addedLocals)
        (⟨fun wire => Var.appendRight outer wire⟩ :
          WireRenaming (hostLocals ++ addedLocals)
            (outer ++ (hostLocals ++ addedLocals)))
        (pinNeeded retained)
      let removed := addedItems.renameWires
        (WireRenaming.comp
          (Region.adjoinMaterialWire outer hostLocals addedLocals)
          (wireMap.appendRight addedLocals))
      let removedPins := pinWires (outer ++ (hostLocals ++ addedLocals))
        WireRenaming.id (removedUsed removed)
      let allPins := removedPins.append pins
      simp only [eraseAt, residue, retainedItems, removedItems]
      change (∀ localIndex : Fin (hostLocals ++ addedLocals).length,
          let paths := (retained.append allPins).incidencePaths
            (outer.length + localIndex.val) 0
          paths ≠ [] ∧ RegionPath.deepestCommonAncestor paths = []) ∧
        (retained.append allPins).ChildrenCanonical
      constructor
      · intro localIndex
        let localWire := Var.ofIndex localIndex
        let retainedPaths := retained.incidencePaths
          (outer.length + localIndex.val) 0
        have pathsEq :
            (retained.append allPins).incidencePaths
                (outer.length + localIndex.val) 0 =
              retainedPaths ++ allPins.incidencePaths
                (outer.length + localIndex.val) retained.length := by
          simpa [retainedPaths] using
            ItemSeq.incidencePaths_append retained allPins
              (outer.length + localIndex.val) 0
        by_cases retainedCanonical : retainedPaths ≠ [] ∧
            RegionPath.deepestCommonAncestor retainedPaths = []
        · rw [pathsEq]
          exact ⟨List.append_ne_nil_of_left_ne_nil retainedCanonical.1 _,
            RegionPath.deepestCommonAncestor_append_eq_nil
              retainedPaths _ retainedCanonical.1 retainedCanonical.2⟩
        · have selected : pinNeeded retained localWire = true := by
            simp [pinNeeded, retainedPaths, retainedCanonical, localWire]
          have localPinContains : [] ∈ pins.incidencePaths
              (outer.length + localIndex.val)
                (retained.length + removedPins.length) := by
            have mappedIndex :
                ((⟨fun wire => Var.appendRight outer wire⟩ :
                  WireRenaming (hostLocals ++ addedLocals)
                    (outer ++ (hostLocals ++ addedLocals)))
                    localWire).index.val =
                  outer.length + localIndex.val := by
              simp [localWire]
            rw [← mappedIndex]
            exact pinWires_mem_nil _ _ _ localWire
              (retained.length + removedPins.length) selected
          have pinContains : [] ∈ allPins.incidencePaths
              (outer.length + localIndex.val) retained.length := by
            rw [show allPins = removedPins.append pins by rfl,
              ItemSeq.incidencePaths_append]
            exact List.mem_append_right _ localPinContains
          rw [pathsEq]
          have contains : [] ∈ retainedPaths ++
              allPins.incidencePaths
                (outer.length + localIndex.val) retained.length :=
            List.mem_append_right retainedPaths pinContains
          exact ⟨List.ne_nil_of_mem contains,
            RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil _ contains⟩
      · apply (ItemSeq.childrenCanonical_append retained allPins).mpr
        constructor
        · have sourceChildren := sourceCanonical.2
          exact (ItemSeq.childrenCanonical_append _ _).mp sourceChildren |>.1
        · apply (ItemSeq.childrenCanonical_append removedPins pins).mpr
          exact ⟨pinWires_childrenCanonical _ _ _,
            pinWires_childrenCanonical _ _ _⟩

inductive Local : LocalRule
  | erase
      (hostLocals : List Sig)
      (hostItems : ItemSeq (wires ++ hostLocals))
      (material : Region materialWires)
      (wireMap : WireRenaming materialWires (wires ++ hostLocals)) :
      Local
        (Region.spliceAt hostLocals hostItems material wireMap)
        (eraseAt hostLocals hostItems material wireMap)

end Erasure

def Erasure : Rule :=
  Contextual Erasure.Local

theorem Erasure.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Erasure source target)
    (targetIso : OpenDiagramIso target target') :
    Erasure source' target' :=
  Contextual.iso sourceIso step targetIso

theorem Erasure.respectsTargetIso
    (step : Erasure source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Erasure source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Erasure.iso (OpenDiagramIso.refl source) step targetIso

theorem Erasure.backward_respectsTargetIso
    (step : Erasure target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Erasure target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Erasure.iso targetIso step (OpenDiagramIso.refl source)

end VisualProof.Rule
