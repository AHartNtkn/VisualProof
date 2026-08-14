import VisualProof.Diagram.Algebra
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

private theorem contextFill_holeCanonical
    (context : DiagramContext outer holeWires) (body : Region holeWires)
    (filledCanonical : (context.fill body).Canonical) : body.Canonical := by
  induction context with
  | hole => exact filledCanonical
  | @cut currentOuter currentHole locals leading trailing child induction =>
      have children :=
        (ItemSeq.childrenCanonical_append leading
          (.cons (.cut (child.fill body)) trailing)).mp filledCanonical.2
      exact induction body children.2.1

private theorem contextFill_canonical_of_nonempty_iff
    (context : DiagramContext outer holeWires)
    (before after : Region holeWires)
    (sourceCanonical : (context.fill before).Canonical)
    (afterCanonical : after.Canonical)
    (holeNonempty : ∀ {signature} (wire : Var holeWires signature),
      before.incidencePaths wire.index.val ≠ [] ↔
        after.incidencePaths wire.index.val ≠ []) :
    (context.fill after).Canonical ∧
      ∀ {signature} (wire : Var outer signature),
        (context.fill before).incidencePaths wire.index.val ≠ [] ↔
          (context.fill after).incidencePaths wire.index.val ≠ [] := by
  induction context with
  | hole => exact ⟨afterCanonical, holeNonempty⟩
  | @cut currentOuter currentHole locals leading trailing child induction =>
      have sourceChildren := sourceCanonical.2
      have leadingAndRest :=
        (ItemSeq.childrenCanonical_append leading
          (.cons (.cut (child.fill before)) trailing)).mp sourceChildren
      have sourceChildCanonical : (child.fill before).Canonical :=
        leadingAndRest.2.1
      have childResult := induction before after sourceChildCanonical
        afterCanonical holeNonempty
      have childCanonical : (child.fill after).Canonical := childResult.1
      constructor
      · constructor
        · intro localIndex
          let localWire := Var.appendRight currentOuter (Var.ofIndex localIndex)
          have childSameNonempty := childResult.2 localWire
          have childSameEmpty :
              (child.fill before).incidencePaths localWire.index.val = [] ↔
                (child.fill after).incidencePaths localWire.index.val = [] := by
            constructor
            · intro sourceEmpty
              by_cases targetEmpty :
                  (child.fill after).incidencePaths localWire.index.val = []
              · exact targetEmpty
              · exact False.elim ((childSameNonempty.mpr targetEmpty) sourceEmpty)
            · intro targetEmpty
              by_cases sourceEmpty :
                  (child.fill before).incidencePaths localWire.index.val = []
              · exact sourceEmpty
              · exact False.elim ((childSameNonempty.mp sourceEmpty) targetEmpty)
          have sourceRoot := sourceCanonical.1 localIndex
          rw [ItemSeq.incidencePaths_frame] at sourceRoot ⊢
          have transformed := (RegionPath.rooted_replace
            (leading.incidencePaths localWire.index.val 0)
            ((child.fill before).incidencePaths localWire.index.val)
            ((child.fill after).incidencePaths localWire.index.val)
            (trailing.incidencePaths localWire.index.val (leading.length + 1))
            leading.length childSameEmpty).mp
              (by simpa [localWire] using sourceRoot)
          simpa [localWire] using transformed
        · apply (ItemSeq.childrenCanonical_append leading
            (.cons (.cut (child.fill after)) trailing)).mpr
          exact ⟨leadingAndRest.1, ⟨childCanonical, leadingAndRest.2.2⟩⟩
      · intro signature wire
        let childWire := wire.appendLeft locals
        have childSameNonempty := childResult.2 childWire
        have childSameEmpty :
            (child.fill before).incidencePaths childWire.index.val = [] ↔
              (child.fill after).incidencePaths childWire.index.val = [] := by
          constructor
          · intro sourceEmpty
            by_cases targetEmpty :
                (child.fill after).incidencePaths childWire.index.val = []
            · exact targetEmpty
            · exact False.elim ((childSameNonempty.mpr targetEmpty) sourceEmpty)
          · intro targetEmpty
            by_cases sourceEmpty :
                (child.fill before).incidencePaths childWire.index.val = []
            · exact sourceEmpty
            · exact False.elim ((childSameNonempty.mp sourceEmpty) targetEmpty)
        simp only [DiagramContext.fill, Region.incidencePaths,
          ItemSeq.incidencePaths_frame]
        simpa [childWire] using RegionPath.nonempty_replace
          (leading.incidencePaths wire.index.val 0)
          ((child.fill before).incidencePaths wire.index.val)
          ((child.fill after).incidencePaths wire.index.val)
          (trailing.incidencePaths wire.index.val (leading.length + 1))
          leading.length (by simpa [childWire] using childSameEmpty)

theorem occurrenceTargetCanonical
    (hostLocals : List Sig) (hostItems : ItemSeq (holeWires ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (holeWires ++ hostLocals))
    (occurrence : Occurrence
      (Region.spliceAt hostLocals hostItems material wireMap) source) :
    (occurrence.context.fill
      (eraseAt hostLocals hostItems material wireMap)).Canonical :=
  (contextFill_canonical_of_nonempty_iff occurrence.context
    (Region.spliceAt hostLocals hostItems material wireMap)
    (eraseAt hostLocals hostItems material wireMap)
    occurrence.sourceCanonical
    (eraseAt_canonical hostLocals hostItems material wireMap
      (contextFill_holeCanonical occurrence.context _
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
