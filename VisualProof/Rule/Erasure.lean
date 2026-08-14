import VisualProof.Diagram.Algebra
import VisualProof.Diagram.Scope.Context
import VisualProof.Diagram.UnaryIdentity
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

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
      (addedItems.renameWires (wireMap.appendRight addedLocals)).renameWires
        (Region.adjoinMaterialWire outer hostLocals addedLocals)

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
  let removedPins := ItemSeq.pinWires
    (outer ++ (hostLocals ++ material.locals)) WireRenaming.id
    (ItemSeq.usesWire removed)
  let localPins := ItemSeq.pinWires (hostLocals ++ material.locals)
    ⟨fun wire => Var.appendRight outer wire⟩
    (fun wire => ItemSeq.needsRootPin retained
      (Var.appendRight outer wire))
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
      let pins := ItemSeq.pinWires (hostLocals ++ addedLocals)
        (⟨fun wire => Var.appendRight outer wire⟩ :
          WireRenaming (hostLocals ++ addedLocals)
            (outer ++ (hostLocals ++ addedLocals)))
        (fun wire => ItemSeq.needsRootPin retained
          (Var.appendRight outer wire))
      let removed :=
        (addedItems.renameWires (wireMap.appendRight addedLocals)).renameWires
          (Region.adjoinMaterialWire outer hostLocals addedLocals)
      let removedPins := ItemSeq.pinWires
        (outer ++ (hostLocals ++ addedLocals)) WireRenaming.id
        (ItemSeq.usesWire removed)
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
        · have selected : ItemSeq.needsRootPin retained
              (Var.appendRight outer localWire) = true := by
            simp [ItemSeq.needsRootPin, retainedPaths, retainedCanonical,
              localWire]
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
            exact ItemSeq.pinWires_mem_nil _ _ _ localWire
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
          exact ⟨ItemSeq.pinWires_childrenCanonical _ _ _,
            ItemSeq.pinWires_childrenCanonical _ _ _⟩

theorem eraseAt_inherited_nonempty_iff
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals))
    (wire : Var outer signature) :
    (Region.spliceAt hostLocals hostItems material wireMap).incidencePaths
        wire.index.val ≠ [] ↔
      (eraseAt hostLocals hostItems material wireMap).incidencePaths
        wire.index.val ≠ [] := by
  cases material with
  | mk addedLocals addedItems =>
      let retained := hostItems.renameWires
        (Region.adjoinHostWire outer hostLocals addedLocals)
      let removed :=
        (addedItems.renameWires (wireMap.appendRight addedLocals)).renameWires
          (Region.adjoinMaterialWire outer hostLocals addedLocals)
      let removedPins := ItemSeq.pinWires
        (outer ++ (hostLocals ++ addedLocals)) WireRenaming.id
        (ItemSeq.usesWire removed)
      let localPins := ItemSeq.pinWires (hostLocals ++ addedLocals)
        (⟨fun localWire => Var.appendRight outer localWire⟩ :
          WireRenaming (hostLocals ++ addedLocals)
            (outer ++ (hostLocals ++ addedLocals)))
        (fun localWire => ItemSeq.needsRootPin retained
          (Var.appendRight outer localWire))
      have localPinsEmpty : localPins.incidencePaths wire.index.val
          (retained.length + removedPins.length) = [] := by
        apply ItemSeq.pinWires_incidence_eq_nil_of
        intro localSignature localWire _
        simp only [Var.index_appendRight]
        omega
      have removedPinsEmptyIff :
          removedPins.incidencePaths wire.index.val retained.length = [] ↔
            removed.incidencePaths wire.index.val 0 = [] := by
        constructor
        · intro pinsEmpty
          by_cases removedEmpty :
              removed.incidencePaths wire.index.val 0 = []
          · exact removedEmpty
          · let sourceWire := wire.appendLeft (hostLocals ++ addedLocals)
            have selected : ItemSeq.usesWire removed sourceWire = true := by
              simp [ItemSeq.usesWire, sourceWire, removedEmpty]
            have contains := ItemSeq.pinWires_mem_nil
              (outer ++ (hostLocals ++ addedLocals)) WireRenaming.id
              (ItemSeq.usesWire removed) sourceWire retained.length selected
            have sourceIndex :
                (WireRenaming.id sourceWire).index.val = wire.index.val := by
              simp [WireRenaming.id, sourceWire]
            rw [sourceIndex, pinsEmpty] at contains
            simp at contains
        · intro removedEmpty
          apply ItemSeq.pinWires_incidence_eq_nil_of
          intro sourceSignature sourceWire selected
          have sourceUsed :
              removed.incidencePaths sourceWire.index.val 0 ≠ [] := by
            simpa [ItemSeq.usesWire] using selected
          intro sameIndex
          apply sourceUsed
          change sourceWire.index.val = wire.index.val at sameIndex
          rw [sameIndex]
          exact removedEmpty
      have pinsEmptyIff :
          (removedPins.append localPins).incidencePaths
              wire.index.val retained.length = [] ↔
            removed.incidencePaths wire.index.val 0 = [] := by
        rw [ItemSeq.incidencePaths_append, localPinsEmpty,
          List.append_nil, removedPinsEmptyIff]
      simp only [Region.spliceAt, Region.renameWires, Region.adjoinAt,
        eraseAt, residue, retainedItems, removedItems, Region.incidencePaths]
      change (retained.append removed).incidencePaths wire.index.val 0 ≠ [] ↔
        (retained.append (removedPins.append localPins)).incidencePaths
          wire.index.val 0 ≠ []
      rw [ItemSeq.incidencePaths_append, ItemSeq.incidencePaths_append]
      have removedShift : removed.incidencePaths wire.index.val retained.length =
          [] ↔ removed.incidencePaths wire.index.val 0 = [] := by
        exact ItemSeq.incidencePaths_eq_nil_iff_itemIndex
          removed wire.index.val retained.length 0
      apply not_congr
      simp only [List.append_eq_nil_iff]
      simp only [Nat.zero_add]
      rw [removedShift, pinsEmptyIff]

theorem occurrenceTargetCanonical
    (hostLocals : List Sig) (hostItems : ItemSeq (holeWires ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (holeWires ++ hostLocals))
    (occurrence : Occurrence
      (Region.spliceAt hostLocals hostItems material wireMap) source) :
    (occurrence.context.fill
      (eraseAt hostLocals hostItems material wireMap)).Canonical :=
  (occurrence.context.replaceCanonical
    (Region.spliceAt hostLocals hostItems material wireMap)
    (eraseAt hostLocals hostItems material wireMap)
    occurrence.sourceCanonical
    (eraseAt_canonical hostLocals hostItems material wireMap
      (occurrence.context.holeCanonical _
        occurrence.sourceCanonical))
    (eraseAt_inherited_nonempty_iff hostLocals hostItems material wireMap)).1

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
