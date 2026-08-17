import VisualProof.Diagram.Algebra
import VisualProof.Diagram.Scope.Context
import VisualProof.Diagram.Scope.Rename
import VisualProof.Diagram.UnaryIdentity
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Erasure

private def removedItems
    (hostLocals : List Sig) (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals)) :
    ItemSeq ((outer ++ hostLocals) ++ material.locals) :=
  match material with
  | .mk addedLocals addedItems =>
      addedItems.renameWires (wireMap.appendRight addedLocals)

/-- Whether the removed material mentions this context wire. -/
private def removedUses
    (hostLocals : List Sig) (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals))
    {signature : Sig} (wire : Var (outer ++ hostLocals) signature) : Bool :=
  ItemSeq.usesWire (removedItems hostLocals material wireMap)
    (wire.appendLeft material.locals)

/-- The ownership residue erasure leaves: one unary identity at the region
for each context wire the removed material used that the retained host
content no longer touches, and one for each of the region's own wires the
retained content no longer roots. Exactly the support the removal took;
the erased material's local wires die with it. -/
def residue
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals)) :
    ItemSeq (outer ++ hostLocals) :=
  (ItemSeq.pinWires (outer ++ hostLocals) WireRenaming.id
    (fun wire => removedUses hostLocals material wireMap wire &&
      !ItemSeq.usesWire hostItems wire)).append
    (ItemSeq.pinWires hostLocals
      ⟨fun wire => Var.appendRight outer wire⟩
      (fun wire => ItemSeq.needsRootPin hostItems
        (Var.appendRight outer wire)))

/-- Erasure keeps the host content and the region's quantified wire owners,
capping with unary identities exactly where the removal took a wire's
support. -/
def eraseAt
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals)) :
    Region outer :=
  .mk hostLocals
    (hostItems.append (residue hostLocals hostItems material wireMap))

theorem eraseAt_canonical
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires) (wireMap : WireRenaming materialWires
      (outer ++ hostLocals))
    (sourceCanonical :
      (Region.spliceAt hostLocals hostItems material wireMap).Canonical) :
    (eraseAt hostLocals hostItems material wireMap).Canonical := by
  cases material with
  | mk addedLocals addedItems =>
      let removed := addedItems.renameWires (wireMap.appendRight addedLocals)
      let orphanPins := ItemSeq.pinWires (outer ++ hostLocals) WireRenaming.id
        (fun wire => ItemSeq.usesWire removed (wire.appendLeft addedLocals) &&
          !ItemSeq.usesWire hostItems wire)
      let localPins := ItemSeq.pinWires hostLocals
        (⟨fun wire => Var.appendRight outer wire⟩ :
          WireRenaming hostLocals (outer ++ hostLocals))
        (fun wire => ItemSeq.needsRootPin hostItems
          (Var.appendRight outer wire))
      let retainedR := hostItems.renameWires
        (Region.adjoinHostWire outer hostLocals addedLocals)
      let removedR := removed.renameWires
        (Region.adjoinMaterialWire outer hostLocals addedLocals)
      have sourceShape :
          Region.spliceAt hostLocals hostItems
              (Region.mk addedLocals addedItems) wireMap =
            Region.mk (hostLocals ++ addedLocals)
              (retainedR.append removedR) := rfl
      rw [sourceShape] at sourceCanonical
      simp only [eraseAt, residue, removedUses, removedItems]
      change (∀ localIndex : Fin hostLocals.length,
          let paths := (hostItems.append
            (orphanPins.append localPins)).incidencePaths
            (outer.length + localIndex.val) 0
          RegionPath.RootedTwo paths) ∧
        (hostItems.append (orphanPins.append localPins)).ChildrenCanonical
      constructor
      · intro localIndex
        let localWire : Var hostLocals hostLocals[localIndex] :=
          Var.ofIndex localIndex
        let hostPaths := hostItems.incidencePaths
          (outer.length + localIndex.val) 0
        have pathsEq :
            (hostItems.append (orphanPins.append localPins)).incidencePaths
                (outer.length + localIndex.val) 0 =
              hostPaths ++ (orphanPins.append localPins).incidencePaths
                (outer.length + localIndex.val) hostItems.length := by
          simpa [hostPaths] using
            ItemSeq.incidencePaths_append hostItems
              (orphanPins.append localPins)
              (outer.length + localIndex.val) 0
        by_cases hostRooted : RegionPath.RootedTwo hostPaths
        · have orphanNil : orphanPins.incidencePaths
              (outer.length + localIndex.val) hostItems.length = [] := by
            apply ItemSeq.pinWires_incidence_eq_nil_of
            intro otherSignature other selectedOther sameIndex
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at selectedOther
            have otherIndex : other.index.val =
                outer.length + localIndex.val := by
              simpa [WireRenaming.id] using sameIndex
            have otherHost : ItemSeq.usesWire hostItems other = true := by
              simp only [ItemSeq.usesWire, decide_eq_true_eq, otherIndex]
              simpa [hostPaths] using hostRooted.nonempty
            rw [otherHost] at selectedOther
            simp at selectedOther
          have localNil : localPins.incidencePaths
              (outer.length + localIndex.val)
              (hostItems.length + orphanPins.length) = [] := by
            apply ItemSeq.pinWires_incidence_eq_nil_of
            intro otherSignature other selectedOther sameIndex
            have otherIndex : other.index.val = localIndex.val := by
              simpa using sameIndex
            simp only [ItemSeq.needsRootPin, decide_eq_true_eq]
              at selectedOther
            apply selectedOther
            have indexEq : (Var.appendRight outer other).index.val =
                outer.length + localIndex.val := by
              simp [otherIndex]
            rw [indexEq]
            simpa [hostPaths] using hostRooted
          rw [pathsEq, ItemSeq.incidencePaths_append, orphanNil, localNil]
          simpa [hostPaths] using hostRooted
        · have localSelectedTrue : ItemSeq.needsRootPin hostItems
              (Var.appendRight outer localWire) = true := by
            simp only [ItemSeq.needsRootPin, decide_eq_true_eq]
            have indexEq : (Var.appendRight outer localWire).index.val =
                outer.length + localIndex.val := by
              simp [localWire]
            rw [indexEq]
            simpa [hostPaths] using hostRooted
          have localMem : [] ∈ localPins.incidencePaths
              (outer.length + localIndex.val)
              (hostItems.length + orphanPins.length) := by
            have mapped : ((⟨fun wire => Var.appendRight outer wire⟩ :
                WireRenaming hostLocals (outer ++ hostLocals))
                  localWire).index.val =
                outer.length + localIndex.val := by
              simp [localWire]
            rw [← mapped]
            exact ItemSeq.pinWires_mem_nil _ _ _ localWire _
              localSelectedTrue
          have contains : [] ∈ (hostItems.append
              (orphanPins.append localPins)).incidencePaths
              (outer.length + localIndex.val) 0 := by
            rw [pathsEq, ItemSeq.incidencePaths_append]
            exact List.mem_append_right _ (List.mem_append_right _ localMem)
          refine ⟨?_,
            RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil _ contains⟩
          by_cases hostEmpty : hostPaths = []
          · have sourceRootedTwo : RegionPath.RootedTwo
                ((retainedR.append removedR).incidencePaths
                  (outer.length + localIndex.val) 0) := by
              have bound : localIndex.val < (hostLocals ++ addedLocals).length := by
                simp only [List.length_append]
                omega
              exact sourceCanonical.1 ⟨localIndex.val, bound⟩
            have retainedBridge : retainedR.incidencePaths
                (outer.length + localIndex.val) 0 = hostPaths := by
              have bridged := ItemSeq.incidencePaths_renameWires_adjoinHost
                (addedLocals := addedLocals) hostItems
                (Var.appendRight outer localWire) 0
              simpa [localWire, hostPaths] using bridged
            have removedNonempty : removedR.incidencePaths
                (outer.length + localIndex.val) retainedR.length ≠ [] := by
              intro removedEmpty
              apply sourceRootedTwo.nonempty
              rw [ItemSeq.incidencePaths_append,
                show retainedR.incidencePaths
                    (outer.length + localIndex.val) 0 = [] from
                  retainedBridge.trans (by simpa [hostPaths] using hostEmpty),
                show removedR.incidencePaths (outer.length + localIndex.val)
                    (0 + retainedR.length) = [] by simpa using removedEmpty]
              rfl
            have removedSelected : ItemSeq.usesWire removed
                ((Var.appendRight outer localWire).appendLeft addedLocals) =
                  true := by
              simp only [ItemSeq.usesWire, decide_eq_true_eq]
              intro removedZeroEmpty
              apply removedNonempty
              have bridged := ItemSeq.incidencePaths_renameWires_adjoinMaterial
                removed ((Var.appendRight outer localWire).appendLeft
                  addedLocals) retainedR.length
              have indexEq : ((Var.appendRight outer
                  localWire).appendLeft addedLocals).index.val =
                  outer.length + localIndex.val := by
                simp [localWire]
              rw [indexEq] at bridged
              rw [bridged]
              exact (ItemSeq.incidencePaths_eq_nil_iff_itemIndex removed
                (outer.length + localIndex.val) retainedR.length 0).mpr
                (by
                  have shifted := removedZeroEmpty
                  rw [indexEq] at shifted
                  exact shifted)
            have hostFalse : ItemSeq.usesWire hostItems
                (Var.appendRight outer localWire) = false := by
              simp only [ItemSeq.usesWire, decide_eq_false_iff_not]
              have indexEq : (Var.appendRight outer localWire).index.val =
                  outer.length + localIndex.val := by
                simp [localWire]
              rw [indexEq]
              intro nonempty
              exact nonempty (by simpa [hostPaths] using hostEmpty)
            have orphanMem : [] ∈ orphanPins.incidencePaths
                (outer.length + localIndex.val) hostItems.length := by
              have mapped : (WireRenaming.id
                  (Var.appendRight outer localWire)).index.val =
                  outer.length + localIndex.val := by
                simp [WireRenaming.id, localWire]
              rw [← mapped]
              apply ItemSeq.pinWires_mem_nil
              simp [removedSelected, hostFalse]
            rw [pathsEq, ItemSeq.incidencePaths_append]
            have orphanPositive : 0 < (orphanPins.incidencePaths
                (outer.length + localIndex.val) hostItems.length).length :=
              List.length_pos_iff.mpr (List.ne_nil_of_mem orphanMem)
            have localPositive : 0 < (localPins.incidencePaths
                (outer.length + localIndex.val)
                (hostItems.length + orphanPins.length)).length :=
              List.length_pos_iff.mpr (List.ne_nil_of_mem localMem)
            simp only [List.length_append]
            omega
          · rw [pathsEq, ItemSeq.incidencePaths_append]
            have hostPositive : 0 < hostPaths.length :=
              List.length_pos_iff.mpr hostEmpty
            have localPositive : 0 < (localPins.incidencePaths
                (outer.length + localIndex.val)
                (hostItems.length + orphanPins.length)).length :=
              List.length_pos_iff.mpr (List.ne_nil_of_mem localMem)
            simp only [List.length_append]
            omega
      · apply (ItemSeq.childrenCanonical_append hostItems
          (orphanPins.append localPins)).mpr
        constructor
        · have sourceChildren := sourceCanonical.2
          have retainedCC := (ItemSeq.childrenCanonical_append retainedR
            removedR).mp sourceChildren |>.1
          exact (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
            hostItems).mp retainedCC
        · apply (ItemSeq.childrenCanonical_append orphanPins localPins).mpr
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
      let removed := addedItems.renameWires (wireMap.appendRight addedLocals)
      let orphanPins := ItemSeq.pinWires (outer ++ hostLocals) WireRenaming.id
        (fun wire => ItemSeq.usesWire removed (wire.appendLeft addedLocals) &&
          !ItemSeq.usesWire hostItems wire)
      let localPins := ItemSeq.pinWires hostLocals
        (⟨fun wire => Var.appendRight outer wire⟩ :
          WireRenaming hostLocals (outer ++ hostLocals))
        (fun wire => ItemSeq.needsRootPin hostItems
          (Var.appendRight outer wire))
      let retainedR := hostItems.renameWires
        (Region.adjoinHostWire outer hostLocals addedLocals)
      let removedR := removed.renameWires
        (Region.adjoinMaterialWire outer hostLocals addedLocals)
      have embeddedIndex : (wire.appendLeft hostLocals).index.val =
          wire.index.val := by simp
      have deepIndex : ((wire.appendLeft hostLocals).appendLeft
          addedLocals).index.val = wire.index.val := by simp
      have localNil : localPins.incidencePaths wire.index.val
          (hostItems.length + orphanPins.length) = [] := by
        apply ItemSeq.pinWires_incidence_eq_nil_of
        intro otherSignature other _ sameIndex
        have shifted : outer.length + other.index.val = wire.index.val := by
          simpa using sameIndex
        have bound := wire.index.isLt
        omega
      have orphanIff : orphanPins.incidencePaths wire.index.val
            hostItems.length ≠ [] ↔
          (ItemSeq.usesWire removed
              ((wire.appendLeft hostLocals).appendLeft addedLocals) &&
            !ItemSeq.usesWire hostItems (wire.appendLeft hostLocals)) =
              true := by
        constructor
        · intro nonempty
          cases selectedCase : (ItemSeq.usesWire removed
              ((wire.appendLeft hostLocals).appendLeft addedLocals) &&
            !ItemSeq.usesWire hostItems (wire.appendLeft hostLocals)) with
          | true => rfl
          | false =>
            exfalso
            apply nonempty
            apply ItemSeq.pinWires_incidence_eq_nil_of
            intro otherSignature other selectedOther sameIndex
            have otherIndex : other.index.val = wire.index.val := by
              simpa [WireRenaming.id] using sameIndex
            have transfer : (ItemSeq.usesWire removed
                ((wire.appendLeft hostLocals).appendLeft addedLocals) &&
              !ItemSeq.usesWire hostItems (wire.appendLeft hostLocals)) =
                true := by
              simp only [Bool.and_eq_true, Bool.not_eq_true']
                at selectedOther ⊢
              refine ⟨?_, ?_⟩
              · have used := selectedOther.1
                simp only [ItemSeq.usesWire, decide_eq_true_eq] at used ⊢
                rw [deepIndex]
                rw [Var.index_appendLeft, otherIndex] at used
                exact used
              · have unused := selectedOther.2
                simp only [ItemSeq.usesWire, decide_eq_false_iff_not]
                  at unused ⊢
                rw [embeddedIndex]
                rw [otherIndex] at unused
                exact unused
            simp [selectedCase] at transfer
        · intro selectedTrue
          intro empty
          have mem := ItemSeq.pinWires_mem_nil (outer ++ hostLocals)
            WireRenaming.id
            (fun wire => ItemSeq.usesWire removed
                (wire.appendLeft addedLocals) &&
              !ItemSeq.usesWire hostItems wire)
            (wire.appendLeft hostLocals) hostItems.length selectedTrue
          have mapped : (WireRenaming.id
              (wire.appendLeft hostLocals)).index.val = wire.index.val := by
            simp [WireRenaming.id]
          rw [mapped, empty] at mem
          simp at mem
      have retainedBridge : retainedR.incidencePaths wire.index.val 0 =
          hostItems.incidencePaths wire.index.val 0 := by
        have bridged := ItemSeq.incidencePaths_renameWires_adjoinHost
          (addedLocals := addedLocals) hostItems
          (wire.appendLeft hostLocals) 0
        simpa [embeddedIndex] using bridged
      have removedBridge : removedR.incidencePaths wire.index.val
            retainedR.length =
          removed.incidencePaths wire.index.val retainedR.length := by
        have bridged := ItemSeq.incidencePaths_renameWires_adjoinMaterial
          removed ((wire.appendLeft hostLocals).appendLeft addedLocals)
          retainedR.length
        simpa [deepIndex] using bridged
      have removedShiftIff : removed.incidencePaths wire.index.val
            retainedR.length = [] ↔
          removed.incidencePaths wire.index.val 0 = [] :=
        ItemSeq.incidencePaths_eq_nil_iff_itemIndex removed
          wire.index.val retainedR.length 0
      have sourceShape :
          Region.spliceAt hostLocals hostItems
              (Region.mk addedLocals addedItems) wireMap =
            Region.mk (hostLocals ++ addedLocals)
              (retainedR.append removedR) := rfl
      rw [sourceShape]
      simp only [eraseAt, residue, removedUses, removedItems]
      change (retainedR.append removedR).incidencePaths wire.index.val 0 ≠ []
        ↔ (hostItems.append (orphanPins.append localPins)).incidencePaths
          wire.index.val 0 ≠ []
      rw [ItemSeq.incidencePaths_append, ItemSeq.incidencePaths_append,
        ItemSeq.incidencePaths_append]
      simp only [Nat.zero_add]
      rw [retainedBridge, removedBridge, localNil, List.append_nil]
      by_cases hostCase :
          hostItems.incidencePaths wire.index.val 0 = []
      · have hostUnused : ItemSeq.usesWire hostItems
            (wire.appendLeft hostLocals) = false := by
          simp only [ItemSeq.usesWire, decide_eq_false_iff_not]
          rw [embeddedIndex]
          intro nonempty
          exact nonempty hostCase
        rw [hostCase]
        simp only [List.nil_append, ne_eq]
        have toOrphanEmpty : removed.incidencePaths wire.index.val
              retainedR.length = [] →
            orphanPins.incidencePaths wire.index.val
              hostItems.length = [] := by
          intro removedEmpty
          apply ItemSeq.pinWires_incidence_eq_nil_of
          intro otherSignature other selectedOther sameIndex
          simp only [Bool.and_eq_true] at selectedOther
          have used := selectedOther.1
          simp only [ItemSeq.usesWire, decide_eq_true_eq] at used
          have otherIndex : other.index.val = wire.index.val := by
            simpa [WireRenaming.id] using sameIndex
          rw [Var.index_appendLeft, otherIndex] at used
          exact used (removedShiftIff.mp removedEmpty)
        have toRemovedEmpty : orphanPins.incidencePaths wire.index.val
              hostItems.length = [] →
            removed.incidencePaths wire.index.val
              retainedR.length = [] := by
          intro orphanEmpty
          rw [removedShiftIff]
          cases removedZero : removed.incidencePaths wire.index.val 0 with
          | nil => rfl
          | cons head tail =>
            exfalso
            refine orphanIff.mpr ?_ orphanEmpty
            simp only [Bool.and_eq_true, Bool.not_eq_true']
            refine ⟨?_, hostUnused⟩
            simp only [ItemSeq.usesWire, decide_eq_true_eq]
            rw [deepIndex]
            simp [removedZero]
        exact ⟨fun removedNe orphanEq => removedNe (toRemovedEmpty orphanEq),
          fun orphanNe removedEq => orphanNe (toOrphanEmpty removedEq)⟩
      · have hostNonempty := hostCase
        constructor
        · intro _
          intro whole
          rcases List.append_eq_nil_iff.mp whole with ⟨hostEmpty, _⟩
          exact hostNonempty hostEmpty
        · intro _
          intro whole
          rcases List.append_eq_nil_iff.mp whole with ⟨hostEmpty, _⟩
          exact hostNonempty hostEmpty

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

theorem occurrenceTargetExternalTwoEnded
    (hostLocals : List Sig) (hostItems : ItemSeq (holeWires ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (holeWires ++ hostLocals))
    (occurrence : Occurrence
      (Region.spliceAt hostLocals hostItems material wireMap) source) :
    OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
      (occurrence.context.fill
        (eraseAt hostLocals hostItems material wireMap)) := by
  let sourceDiagram := occurrence.interface.withBody
    (occurrence.context.fill
      (Region.spliceAt hostLocals hostItems material wireMap))
    occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
  apply sourceDiagram.externalTwoEnded_of_nonempty_iff
  exact (occurrence.context.replaceCanonical
    (Region.spliceAt hostLocals hostItems material wireMap)
    (eraseAt hostLocals hostItems material wireMap)
    occurrence.sourceCanonical
    (eraseAt_canonical hostLocals hostItems material wireMap
      (occurrence.context.holeCanonical _ occurrence.sourceCanonical))
    (eraseAt_inherited_nonempty_iff hostLocals hostItems material wireMap)).2

theorem occurrenceInsertedExternalTwoEnded
    (hostLocals : List Sig) (hostItems : ItemSeq (holeWires ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (holeWires ++ hostLocals))
    (occurrence : Occurrence
      (eraseAt hostLocals hostItems material wireMap) source)
    (targetCanonical : (occurrence.context.fill
      (Region.spliceAt hostLocals hostItems material wireMap)).Canonical) :
    OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.spliceAt hostLocals hostItems material wireMap)) := by
  let sourceDiagram := occurrence.interface.withBody
    (occurrence.context.fill
      (eraseAt hostLocals hostItems material wireMap))
    occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
  apply sourceDiagram.externalTwoEnded_of_nonempty_iff
  exact (occurrence.context.replaceCanonical
    (eraseAt hostLocals hostItems material wireMap)
    (Region.spliceAt hostLocals hostItems material wireMap)
    occurrence.sourceCanonical
    (occurrence.context.holeCanonical _ targetCanonical)
    (fun wire => (eraseAt_inherited_nonempty_iff hostLocals hostItems
      material wireMap wire).symm)).2

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
