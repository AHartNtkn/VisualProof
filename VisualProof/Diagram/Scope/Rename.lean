import VisualProof.Diagram.Algebra

namespace VisualProof.Diagram

open VisualProof.Theory

private structure ReflectsIndex (rename : WireRenaming source target)
    (sourceIndex targetIndex : Nat) : Prop where
  apply : ∀ {signature} (wire : Var source signature),
    (rename wire).index.val = targetIndex ↔ wire.index.val = sourceIndex
  sourceBound : sourceIndex < source.length
  targetBound : targetIndex < target.length

private theorem Vars.countIndex_map_of_reflect
    (variables : Vars source signatures) (rename : WireRenaming source target)
    (sourceIndex targetIndex : Nat)
    (reflects : ReflectsIndex rename sourceIndex targetIndex) :
    (variables.map (fun wire => rename wire)).countIndex targetIndex =
      variables.countIndex sourceIndex := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      change (if (rename head).index.val = targetIndex then 1 else 0) +
          (tail.map (fun wire => rename wire)).countIndex targetIndex =
        (if head.index.val = sourceIndex then 1 else 0) +
          tail.countIndex sourceIndex
      have headIff := reflects.apply head
      by_cases sourceEq : head.index.val = sourceIndex
      · have targetEq := headIff.mpr sourceEq
        simp only [sourceEq, targetEq, if_true, induction]
      · have targetNe := not_congr headIff |>.mpr sourceEq
        simp only [sourceEq, targetNe, if_false, induction]

private theorem Vars.countIndex_map_eq_zero_of_no_preimage
    (variables : Vars source signatures) (rename : WireRenaming source target)
    (targetIndex : Nat)
    (noPreimage : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val ≠ targetIndex) :
    (variables.map (fun wire => rename wire)).countIndex targetIndex = 0 := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      change (if (rename head).index.val = targetIndex then 1 else 0) +
          (tail.map (fun wire => rename wire)).countIndex targetIndex = 0
      simp [noPreimage head, induction]

private theorem countPorts_map_eq_zero_of_no_preimage
    (arity : Nat) (ports : Fin arity → Var source signature)
    (rename : WireRenaming source target) (targetIndex : Nat)
    (noPreimage : ∀ {wireSignature} (wire : Var source wireSignature),
      (rename wire).index.val ≠ targetIndex) :
    (List.ofFn fun index : Fin arity =>
      (rename (ports index)).index.val).count targetIndex = 0 := by
  induction arity with
  | zero => rfl
  | succ arity induction =>
      rw [List.ofFn_succ]
      have tail := induction (fun index => ports index.succ)
      have headNe := noPreimage (ports 0)
      simp [List.count_cons, headNe, tail]

private theorem countPorts_of_reflect
    (arity : Nat) (ports : Fin arity → Var source signature)
    (rename : WireRenaming source target) (sourceIndex targetIndex : Nat)
    (reflects : ReflectsIndex rename sourceIndex targetIndex) :
    (List.ofFn fun index : Fin arity => (rename (ports index)).index.val).count
        targetIndex =
      (List.ofFn fun index : Fin arity => (ports index).index.val).count
        sourceIndex := by
  induction arity with
  | zero => rfl
  | succ arity induction =>
      rw [List.ofFn_succ, List.ofFn_succ]
      have tailEq := induction (fun index => ports index.succ)
      have headIff := reflects.apply (ports 0)
      by_cases sourceEq : (ports 0).index.val = sourceIndex
      · have targetEq := headIff.mpr sourceEq
        simp [sourceEq, targetEq, tailEq]
      · have targetNe := not_congr headIff |>.mpr sourceEq
        simp [sourceEq, targetNe, tailEq]

private theorem ItemSeq.incidencePaths_rename_reflect
    (items : ItemSeq source) (rename : WireRenaming source target)
    (sourceIndex targetIndex itemIndex : Nat)
    (reflects : ReflectsIndex rename sourceIndex targetIndex) :
    (items.renameWires rename).incidencePaths targetIndex itemIndex =
      items.incidencePaths sourceIndex itemIndex := by
  let regionMotive := fun (source : List Sig) (region : Region source) =>
    ∀ {target} (rename : WireRenaming source target) sourceIndex targetIndex,
      ReflectsIndex rename sourceIndex targetIndex →
        (region.renameWires rename).incidencePaths targetIndex =
          region.incidencePaths sourceIndex
  let itemMotive := fun (source : List Sig) (item : Item source) =>
    ∀ {target} (rename : WireRenaming source target) sourceIndex targetIndex
      itemIndex, ReflectsIndex rename sourceIndex targetIndex →
        (item.renameWires rename).incidencePaths targetIndex itemIndex =
          item.incidencePaths sourceIndex itemIndex
  let itemsMotive := fun (source : List Sig) (items : ItemSeq source) =>
    ∀ {target} (rename : WireRenaming source target) sourceIndex targetIndex
      itemIndex, ReflectsIndex rename sourceIndex targetIndex →
        (items.renameWires rename).incidencePaths targetIndex itemIndex =
          items.incidencePaths sourceIndex itemIndex
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (by
      intro source locals nested nestedIH target rename sourceIndex targetIndex reflect
      simp only [Region.renameWires, Region.incidencePaths]
      apply nestedIH
      exact {
        apply := by
          intro wireSignature wire
          apply Var.appendCases
            (motive := fun wire =>
              ((rename.appendRight locals) wire).index.val = targetIndex ↔
                wire.index.val = sourceIndex)
          · intro sig inherited
            simpa [WireRenaming.appendRight] using reflect.apply inherited
          · intro sig localWire
            simp only [WireRenaming.appendRight, Var.appendMap_right,
              Var.index_appendRight]
            constructor <;> intro equality
            · have : target.length ≤ targetIndex := by omega
              exact False.elim (Nat.not_le_of_lt reflect.targetBound this)
            · have : source.length ≤ sourceIndex := by omega
              exact False.elim (Nat.not_le_of_lt reflect.sourceBound this)
        sourceBound := by
          simpa only [List.length_append] using Nat.lt_of_lt_of_le
            reflect.sourceBound (Nat.le_add_right source.length locals.length)
        targetBound := by
          simpa only [List.length_append] using Nat.lt_of_lt_of_le
            reflect.targetBound (Nat.le_add_right target.length locals.length)
      })
    (by
      intro source arguments head ports target rename sourceIndex targetIndex
        itemIndex reflect
      simp only [Item.renameWires, Item.incidencePaths]
      have portsEq := Vars.countIndex_map_of_reflect ports rename sourceIndex
        targetIndex reflect
      by_cases sourceEq : head.index.val = sourceIndex
      · have targetEq := (reflect.apply head).mpr sourceEq
        simp [sourceEq, targetEq, portsEq]
      · have targetNe := not_congr (reflect.apply head) |>.mpr sourceEq
        simp [sourceEq, targetNe, portsEq])
    (by
      intro source signature arity ports target rename sourceIndex targetIndex
        itemIndex reflect
      simp only [Item.renameWires, Item.incidencePaths]
      rw [countPorts_of_reflect arity ports rename sourceIndex targetIndex reflect])
    (by
      intro source body bodyIH target rename sourceIndex targetIndex itemIndex reflect
      simp only [Item.renameWires, Item.incidencePaths]
      rw [bodyIH rename sourceIndex targetIndex reflect])
    (by intro source target rename sourceIndex targetIndex itemIndex reflect; rfl)
    (by
      intro source head tail headIH tailIH target rename sourceIndex targetIndex
        itemIndex reflect
      simp only [ItemSeq.renameWires, ItemSeq.incidencePaths]
      rw [headIH rename sourceIndex targetIndex itemIndex reflect,
        tailIH rename sourceIndex targetIndex (itemIndex + 1) reflect])
    items rename sourceIndex targetIndex itemIndex reflects

/-- Incidence paths are preserved at any source/target index pair reflected
exactly by a wire renaming. -/
theorem ItemSeq.incidencePaths_renameWires_of_index_iff
    (items : ItemSeq source) (rename : WireRenaming source target)
    (sourceIndex targetIndex itemIndex : Nat)
    (sourceBound : sourceIndex < source.length)
    (targetBound : targetIndex < target.length)
    (reflects : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val = targetIndex ↔
        wire.index.val = sourceIndex) :
    (items.renameWires rename).incidencePaths targetIndex itemIndex =
      items.incidencePaths sourceIndex itemIndex := by
  exact ItemSeq.incidencePaths_rename_reflect items rename sourceIndex
    targetIndex itemIndex ⟨reflects, sourceBound, targetBound⟩

/-- A target wire with no source preimage has no incidences after renaming. -/
theorem ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
    (items : ItemSeq source) (rename : WireRenaming source target)
    (targetIndex itemIndex : Nat) (targetBound : targetIndex < target.length)
    (noPreimage : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val ≠ targetIndex) :
    (items.renameWires rename).incidencePaths targetIndex itemIndex = [] := by
  let regionMotive := fun (source : List Sig) (region : Region source) =>
    ∀ {target} (rename : WireRenaming source target) targetIndex,
      targetIndex < target.length →
      (∀ {signature} (wire : Var source signature),
        (rename wire).index.val ≠ targetIndex) →
      (region.renameWires rename).incidencePaths targetIndex = []
  let itemMotive := fun (source : List Sig) (item : Item source) =>
    ∀ {target} (rename : WireRenaming source target) targetIndex itemIndex,
      targetIndex < target.length →
      (∀ {signature} (wire : Var source signature),
        (rename wire).index.val ≠ targetIndex) →
      (item.renameWires rename).incidencePaths targetIndex itemIndex = []
  let itemsMotive := fun (source : List Sig) (items : ItemSeq source) =>
    ∀ {target} (rename : WireRenaming source target) targetIndex itemIndex,
      targetIndex < target.length →
      (∀ {signature} (wire : Var source signature),
        (rename wire).index.val ≠ targetIndex) →
      (items.renameWires rename).incidencePaths targetIndex itemIndex = []
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (by
      intro source locals nested nestedIH target rename targetIndex bound none
      simp only [Region.renameWires, Region.incidencePaths]
      apply nestedIH (rename.appendRight locals) targetIndex
      · simpa only [List.length_append] using
          Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _)
      · intro signature wire
        apply Var.appendCases (left := source) (right := locals)
          (motive := fun wire =>
            ((rename.appendRight locals) wire).index.val ≠ targetIndex)
        · intro inheritedSignature inherited
          simpa [WireRenaming.appendRight] using none inherited
        · intro localSignature localWire
          simp only [WireRenaming.appendRight, Var.appendMap_right,
            Var.index_appendRight]
          omega)
    (by
      intro source arguments head ports target rename targetIndex itemIndex
        bound none
      simp only [Item.renameWires, Item.incidencePaths]
      rw [Vars.countIndex_map_eq_zero_of_no_preimage ports rename targetIndex none]
      simp [none head])
    (by
      intro source signature arity ports target rename targetIndex itemIndex
        bound none
      simp only [Item.renameWires, Item.incidencePaths]
      rw [countPorts_map_eq_zero_of_no_preimage arity ports rename
        targetIndex none]
      rfl)
    (by
      intro source body bodyIH target rename targetIndex itemIndex bound none
      simp only [Item.renameWires, Item.incidencePaths]
      rw [bodyIH rename targetIndex bound none]
      rfl)
    (by intro source target rename targetIndex itemIndex bound none; rfl)
    (by
      intro source head tail headIH tailIH target rename targetIndex itemIndex
        bound none
      simp only [ItemSeq.renameWires, ItemSeq.incidencePaths]
      rw [headIH rename targetIndex itemIndex bound none,
        tailIH rename targetIndex (itemIndex + 1) bound none]
      rfl)
    items rename targetIndex itemIndex targetBound noPreimage

private theorem appendRight_reflects_local
    (rename : WireRenaming source target) (locals : List Sig)
    (localIndex : Fin locals.length) :
    ReflectsIndex (rename.appendRight locals)
      (source.length + localIndex.val) (target.length + localIndex.val) := by
  refine ⟨?_, by simp, by simp⟩
  intro signature wire
  apply Var.appendCases (left := source) (right := locals)
    (motive := fun wire =>
      ((rename.appendRight locals) wire).index.val =
          target.length + localIndex.val ↔
        wire.index.val = source.length + localIndex.val)
  · intro inheritedSignature inherited
    have targetLt := (rename inherited).index.isLt
    have sourceLt := inherited.index.isLt
    simp only [WireRenaming.appendRight, Var.appendMap_left,
      Var.index_appendLeft]
    constructor <;> intro equality <;> omega
  · intro localSignature localWire
    simp only [WireRenaming.appendRight, Var.appendMap_right,
      Var.index_appendRight]
    omega

private theorem ItemSeq.childrenCanonical_rename
    (items : ItemSeq source) (rename : WireRenaming source target) :
    (items.renameWires rename).ChildrenCanonical ↔ items.ChildrenCanonical := by
  let regionMotive := fun (source : List Sig) (region : Region source) =>
    ∀ {target} (rename : WireRenaming source target),
      ((region.renameWires rename).Canonical ↔ region.Canonical)
  let itemMotive := fun (source : List Sig) (item : Item source) =>
    ∀ {target} (rename : WireRenaming source target),
      ((item.renameWires rename).ChildrenCanonical ↔ item.ChildrenCanonical)
  let itemsMotive := fun (source : List Sig) (items : ItemSeq source) =>
    ∀ {target} (rename : WireRenaming source target),
      ((items.renameWires rename).ChildrenCanonical ↔ items.ChildrenCanonical)
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (by
      intro source locals nested nestedIH target rename
      simp only [Region.renameWires, Region.Canonical]
      have rootsIff : ∀ localIndex : Fin locals.length,
          RegionPath.RootedTwo
              ((nested.renameWires (rename.appendRight locals)).incidencePaths
                (target.length + localIndex.val) 0) ↔
            RegionPath.RootedTwo
              (nested.incidencePaths (source.length + localIndex.val) 0) := by
        intro localIndex
        rw [ItemSeq.incidencePaths_rename_reflect nested
          (rename.appendRight locals)
          (source.length + localIndex.val)
          (target.length + localIndex.val) 0
          (appendRight_reflects_local rename locals localIndex)]
      constructor
      · rintro ⟨roots, children⟩
        exact ⟨fun localIndex => (rootsIff localIndex).mp (roots localIndex),
          (nestedIH (rename.appendRight locals)).mp children⟩
      · rintro ⟨roots, children⟩
        exact ⟨fun localIndex => (rootsIff localIndex).mpr (roots localIndex),
          (nestedIH (rename.appendRight locals)).mpr children⟩)
    (by intro source arguments head ports target rename; exact Iff.rfl)
    (by intro source signature arity ports target rename; exact Iff.rfl)
    (by intro source body bodyIH target rename; exact bodyIH rename)
    (by intro source target rename; exact Iff.rfl)
    (by
      intro source head tail headIH tailIH target rename
      simp only [ItemSeq.renameWires, ItemSeq.ChildrenCanonical]
      rw [headIH rename, tailIH rename])
    items rename

theorem ItemSeq.ChildrenCanonical.renameWires_iff
    (items : ItemSeq source) (rename : WireRenaming source target) :
    (items.renameWires rename).ChildrenCanonical ↔ items.ChildrenCanonical :=
  ItemSeq.childrenCanonical_rename items rename

/-- Renaming inherited wires, including by a noninjective map, does not
change canonicality of locally owned wires or nested regions. -/
theorem Region.Canonical.renameWires_iff
    (region : Region source) (rename : WireRenaming source target) :
    (region.renameWires rename).Canonical ↔ region.Canonical := by
  cases region with
  | mk locals items =>
      simp only [Region.renameWires, Region.Canonical]
      have rootsIff : ∀ localIndex : Fin locals.length,
          RegionPath.RootedTwo
              ((items.renameWires (rename.appendRight locals)).incidencePaths
                (target.length + localIndex.val) 0) ↔
            RegionPath.RootedTwo
              (items.incidencePaths (source.length + localIndex.val) 0) := by
        intro localIndex
        rw [ItemSeq.incidencePaths_rename_reflect items
          (rename.appendRight locals)
          (source.length + localIndex.val)
          (target.length + localIndex.val) 0
          (appendRight_reflects_local rename locals localIndex)]
      constructor
      · rintro ⟨roots, children⟩
        exact ⟨fun localIndex => (rootsIff localIndex).mp (roots localIndex),
          (ItemSeq.childrenCanonical_rename items
            (rename.appendRight locals)).mp children⟩
      · rintro ⟨roots, children⟩
        exact ⟨fun localIndex => (rootsIff localIndex).mpr (roots localIndex),
          (ItemSeq.childrenCanonical_rename items
            (rename.appendRight locals)).mpr children⟩

private def IndexEmbedding (rename : WireRenaming source target) : Prop :=
  ∀ {signature} (wire : Var source signature),
    ReflectsIndex rename wire.index.val (rename wire).index.val

private theorem IndexEmbedding.appendRight
    {source target : List Sig} {rename : WireRenaming source target}
    (embedding : IndexEmbedding rename) (locals : List Sig) :
    IndexEmbedding (rename.appendRight locals) := by
  intro signature selected
  refine ⟨?_, selected.index.isLt,
    (rename.appendRight locals selected).index.isLt⟩
  intro otherSignature other
  apply Var.appendCases (motive := fun selected => ∀ {otherSignature}
    (other : Var (source ++ locals) otherSignature),
    ((rename.appendRight locals) other).index.val =
        ((rename.appendRight locals) selected).index.val ↔
      other.index.val = selected.index.val)
  · intro selectedSignature selectedInherited otherSignature other
    apply Var.appendCases (motive := fun other =>
      ((rename.appendRight locals) other).index.val =
          ((rename.appendRight locals) (selectedInherited.appendLeft locals)).index.val ↔
        other.index.val = (selectedInherited.appendLeft locals).index.val)
    · intro signature inherited
      simpa [WireRenaming.appendRight] using
        (embedding selectedInherited).apply inherited
    · intro signature localWire
      simp only [WireRenaming.appendRight, Var.appendMap_left,
        Var.appendMap_right, Var.index_appendLeft, Var.index_appendRight]
      constructor <;> intro equality <;> omega
  · intro selectedSignature selectedLocal otherSignature other
    apply Var.appendCases (motive := fun other =>
      ((rename.appendRight locals) other).index.val =
          ((rename.appendRight locals) (Var.appendRight source selectedLocal)).index.val ↔
        other.index.val = (Var.appendRight source selectedLocal).index.val)
    · intro signature inherited
      simp only [WireRenaming.appendRight, Var.appendMap_left,
        Var.appendMap_right, Var.index_appendLeft, Var.index_appendRight]
      constructor <;> intro equality <;> omega
    · intro signature localWire
      simp only [WireRenaming.appendRight, Var.appendMap_right,
        Var.index_appendRight]
      omega

private theorem ItemSeq.childrenCanonical_rename_embedding
    (items : ItemSeq source) (rename : WireRenaming source target)
    (embedding : IndexEmbedding rename) :
    (items.renameWires rename).ChildrenCanonical ↔ items.ChildrenCanonical := by
  let regionMotive := fun (source : List Sig) (region : Region source) =>
    ∀ {target} (rename : WireRenaming source target), IndexEmbedding rename →
      ((region.renameWires rename).Canonical ↔ region.Canonical)
  let itemMotive := fun (source : List Sig) (item : Item source) =>
    ∀ {target} (rename : WireRenaming source target), IndexEmbedding rename →
      ((item.renameWires rename).ChildrenCanonical ↔ item.ChildrenCanonical)
  let itemsMotive := fun (source : List Sig) (items : ItemSeq source) =>
    ∀ {target} (rename : WireRenaming source target), IndexEmbedding rename →
      ((items.renameWires rename).ChildrenCanonical ↔ items.ChildrenCanonical)
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (by
      intro source locals nested nestedIH target rename embedding
      have rootsIff : ∀ localIndex : Fin locals.length,
          RegionPath.RootedTwo
              ((nested.renameWires (rename.appendRight locals)).incidencePaths
                (target.length + localIndex.val) 0) ↔
            RegionPath.RootedTwo
              (nested.incidencePaths (source.length + localIndex.val) 0) := by
        intro localIndex
        let sourceWire := Var.appendRight source (Var.ofIndex localIndex)
        have pathsEq := ItemSeq.incidencePaths_rename_reflect nested
          (rename.appendRight locals) sourceWire.index.val
          ((rename.appendRight locals) sourceWire).index.val 0
          (embedding.appendRight locals sourceWire)
        have sourceIndexEq : sourceWire.index.val =
            source.length + localIndex.val := by simp [sourceWire]
        have targetIndexEq : ((rename.appendRight locals) sourceWire).index.val =
            target.length + localIndex.val := by
          simp [sourceWire, WireRenaming.appendRight]
        rw [← targetIndexEq, pathsEq, sourceIndexEq]
      constructor
      · rintro ⟨roots, children⟩
        exact ⟨fun localIndex => (rootsIff localIndex).mp (roots localIndex),
          (nestedIH (rename.appendRight locals)
            (embedding.appendRight locals)).mp children⟩
      · rintro ⟨roots, children⟩
        exact ⟨fun localIndex => (rootsIff localIndex).mpr (roots localIndex),
          (nestedIH (rename.appendRight locals)
            (embedding.appendRight locals)).mpr children⟩)
    (by
      intro source arguments head ports target rename embedding
      exact Iff.rfl)
    (by
      intro source signature arity ports target rename embedding
      exact Iff.rfl)
    (by
      intro source body bodyIH target rename embedding
      exact bodyIH rename embedding)
    (by
      intro source target rename embedding
      exact Iff.rfl)
    (by
      intro source head tail headIH tailIH target rename embedding
      simp only [ItemSeq.renameWires, ItemSeq.ChildrenCanonical]
      rw [headIH rename embedding, tailIH rename embedding])
    items rename embedding

private theorem indexEmbedding_of_preservesIndex
    (rename : WireRenaming source target)
    (_length_eq : source.length = target.length)
    (preserves : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val = wire.index.val) :
    IndexEmbedding rename := by
  intro signature selected
  exact {
    apply := by
      intro otherSignature other
      rw [preserves other, preserves selected]
    sourceBound := selected.index.isLt
    targetBound := (rename selected).index.isLt
  }

theorem ItemSeq.incidencePaths_renameWires_preservesIndex
    (items : ItemSeq source) (rename : WireRenaming source target)
    (length_eq : source.length = target.length)
    (preserves : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val = wire.index.val)
    (wire : Var source signature) (itemIndex : Nat) :
    (items.renameWires rename).incidencePaths wire.index.val itemIndex =
      items.incidencePaths wire.index.val itemIndex := by
  apply ItemSeq.incidencePaths_rename_reflect
  simpa [preserves wire] using
    indexEmbedding_of_preservesIndex rename length_eq preserves wire

theorem ItemSeq.ChildrenCanonical.renameWires_preservesIndex_iff
    (items : ItemSeq source) (rename : WireRenaming source target)
    (length_eq : source.length = target.length)
    (preserves : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val = wire.index.val) :
    (items.renameWires rename).ChildrenCanonical ↔ items.ChildrenCanonical :=
  ItemSeq.childrenCanonical_rename_embedding items rename
    (@indexEmbedding_of_preservesIndex source target rename length_eq preserves)

theorem Region.Canonical.renameWires_preservesIndex_iff
    (region : Region source) (rename : WireRenaming source target)
    (length_eq : source.length = target.length)
    (preserves : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val = wire.index.val) :
    (region.renameWires rename).Canonical ↔ region.Canonical := by
  cases region with
  | mk locals items =>
      simp only [Region.renameWires, Region.Canonical]
      have embedding := @indexEmbedding_of_preservesIndex source target rename
        length_eq preserves
      have rootsIff : ∀ localIndex : Fin locals.length,
          RegionPath.RootedTwo
              ((items.renameWires (rename.appendRight locals)).incidencePaths
                (target.length + localIndex.val) 0) ↔
            RegionPath.RootedTwo
              (items.incidencePaths (source.length + localIndex.val) 0) := by
        intro localIndex
        let wire := Var.appendRight source (Var.ofIndex localIndex)
        have pathsEq := ItemSeq.incidencePaths_rename_reflect items
          (rename.appendRight locals) wire.index.val
          ((rename.appendRight locals) wire).index.val 0
          (embedding.appendRight locals wire)
        have sourceIndex : wire.index.val = source.length + localIndex.val := by
          simp [wire]
        have targetIndex :
            ((rename.appendRight locals) wire).index.val =
              target.length + localIndex.val := by
          simp [wire, WireRenaming.appendRight]
        rw [← targetIndex, pathsEq, sourceIndex]
      constructor
      · rintro ⟨roots, children⟩
        exact ⟨fun localIndex => (rootsIff localIndex).mp (roots localIndex),
          (ItemSeq.childrenCanonical_rename_embedding items
            (rename.appendRight locals) (embedding.appendRight locals)).mp children⟩
      · rintro ⟨roots, children⟩
        exact ⟨fun localIndex => (rootsIff localIndex).mpr (roots localIndex),
          (ItemSeq.childrenCanonical_rename_embedding items
            (rename.appendRight locals) (embedding.appendRight locals)).mpr children⟩

private theorem adjoinHost_index (wire : Var (outer ++ hostLocals) signature) :
    (Region.adjoinHostWire outer hostLocals addedLocals wire).index.val =
      wire.index.val := by
  apply Var.appendCases (left := outer) (right := hostLocals)
    (motive := fun wire =>
      (Region.adjoinHostWire outer hostLocals addedLocals wire).index.val =
        wire.index.val)
  · intros; simp [Region.adjoinHostWire, Region.conjoinLeftWire]
  · intros; simp [Region.adjoinHostWire, Region.conjoinLeftWire]

private theorem adjoinHost_embedding (outer hostLocals addedLocals : List Sig) :
    IndexEmbedding (Region.adjoinHostWire outer hostLocals addedLocals) := by
  intro signature selected
  exact ⟨fun other => by simp only [adjoinHost_index], selected.index.isLt,
    (Region.adjoinHostWire outer hostLocals addedLocals selected).index.isLt⟩

theorem ItemSeq.incidencePaths_renameWires_adjoinHost
    (items : ItemSeq (outer ++ hostLocals))
    (wire : Var (outer ++ hostLocals) signature) (itemIndex : Nat) :
    (items.renameWires
      (Region.adjoinHostWire outer hostLocals addedLocals)).incidencePaths
        wire.index.val itemIndex =
      items.incidencePaths wire.index.val itemIndex := by
  apply ItemSeq.incidencePaths_rename_reflect
  simpa only [adjoinHost_index] using
    adjoinHost_embedding outer hostLocals addedLocals wire

theorem ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
    (items : ItemSeq (outer ++ hostLocals)) :
    (items.renameWires
      (Region.adjoinHostWire outer hostLocals addedLocals)).ChildrenCanonical ↔
        items.ChildrenCanonical :=
  ItemSeq.childrenCanonical_rename_embedding items _
    (adjoinHost_embedding outer hostLocals addedLocals)

theorem Region.Canonical.renameWires_adjoinHost_iff
    (region : Region (outer ++ hostLocals)) :
    (region.renameWires
      (Region.adjoinHostWire outer hostLocals addedLocals)).Canonical ↔
        region.Canonical := by
  let wrapper : ItemSeq (outer ++ hostLocals) := .cons (.cut region) .nil
  have wrapperIff := ItemSeq.childrenCanonical_rename_embedding wrapper _
    (adjoinHost_embedding outer hostLocals addedLocals)
  simpa only [wrapper, ItemSeq.renameWires, Item.renameWires,
    ItemSeq.ChildrenCanonical, Item.ChildrenCanonical, and_true] using wrapperIff

private theorem adjoinMaterial_index
    (wire : Var ((outer ++ hostLocals) ++ addedLocals) signature) :
    (Region.adjoinMaterialWire outer hostLocals addedLocals wire).index.val =
      wire.index.val := by
  apply Var.appendCases (left := outer ++ hostLocals) (right := addedLocals)
    (motive := fun wire =>
      (Region.adjoinMaterialWire outer hostLocals addedLocals wire).index.val =
        wire.index.val)
  · intro signature contextWire
    refine Var.appendCases (left := outer) (right := hostLocals)
      (motive := fun contextWire =>
        (Region.adjoinMaterialWire outer hostLocals addedLocals
            ((contextWire).appendLeft addedLocals)).index.val =
          ((contextWire).appendLeft addedLocals).index.val)
      ?_ ?_ contextWire
    · intro signature outerWire
      simp [Region.adjoinMaterialWire]
    · intro signature localWire
      simp [Region.adjoinMaterialWire]
  · intro signature materialWire
    simp [Region.adjoinMaterialWire, List.length_append, Nat.add_assoc]

private theorem adjoinMaterial_embedding
    (outer hostLocals addedLocals : List Sig) :
    IndexEmbedding (Region.adjoinMaterialWire outer hostLocals addedLocals) :=
  indexEmbedding_of_preservesIndex _
    (by simp [List.length_append])
    (fun wire => adjoinMaterial_index wire)

theorem ItemSeq.incidencePaths_renameWires_adjoinMaterial
    (items : ItemSeq ((outer ++ hostLocals) ++ addedLocals))
    (wire : Var ((outer ++ hostLocals) ++ addedLocals) signature)
    (itemIndex : Nat) :
    (items.renameWires
      (Region.adjoinMaterialWire outer hostLocals addedLocals)).incidencePaths
        wire.index.val itemIndex =
      items.incidencePaths wire.index.val itemIndex := by
  apply ItemSeq.incidencePaths_rename_reflect
  simpa only [adjoinMaterial_index] using
    adjoinMaterial_embedding outer hostLocals addedLocals wire

/-- Canonicality of an adjoined region always contains canonicality of the
material's own locals, independently of how its inherited wires are shared. -/
theorem Region.Canonical.material_of_adjoinAt
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals))
    (canonical : (Region.adjoinAt hostLocals hostItems material).Canonical) :
    material.Canonical := by
  cases material with
  | mk addedLocals addedItems =>
      simp only [Region.adjoinAt, Region.Canonical] at canonical ⊢
      constructor
      · intro localIndex
        let combinedIndex : Fin (hostLocals ++ addedLocals).length :=
          ⟨hostLocals.length + localIndex.val, by
            simp only [List.length_append]
            omega⟩
        let materialWire := Var.appendRight (outer ++ hostLocals)
          (Var.ofIndex localIndex)
        have combinedRoot := canonical.1 combinedIndex
        have wireIndexEq : outer.length + combinedIndex.val =
            materialWire.index.val := by
          simp [combinedIndex, materialWire, List.length_append,
            Nat.add_assoc]
        rw [wireIndexEq, ItemSeq.incidencePaths_append] at combinedRoot
        have hostEmpty :
            (hostItems.renameWires
              (Region.adjoinHostWire outer hostLocals addedLocals)).incidencePaths
                materialWire.index.val 0 = [] := by
          apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
          · have materialIndex : materialWire.index.val =
                (outer ++ hostLocals).length + localIndex.val := by
              simp [materialWire]
            rw [materialIndex]
            simp only [List.length_append]
            omega
          · intro signature wire
            rw [adjoinHost_index]
            have wireBound := wire.index.isLt
            have materialIndex : materialWire.index.val =
                (outer ++ hostLocals).length + localIndex.val := by
              simp [materialWire]
            rw [materialIndex]
            simp only [List.length_append] at wireBound ⊢
            omega
        rw [hostEmpty, List.nil_append] at combinedRoot
        have materialPaths :=
          ItemSeq.incidencePaths_renameWires_adjoinMaterial
            (outer := outer) (hostLocals := hostLocals)
            (addedLocals := addedLocals) addedItems materialWire
            ((hostItems.renameWires
              (Region.adjoinHostWire outer hostLocals addedLocals)).length)
        have materialPaths' :
            (addedItems.renameWires
              (Region.adjoinMaterialWire outer hostLocals addedLocals)).incidencePaths
                materialWire.index.val
                (0 + (hostItems.renameWires
                  (Region.adjoinHostWire outer hostLocals addedLocals)).length) =
              addedItems.incidencePaths materialWire.index.val
                (0 + (hostItems.renameWires
                  (Region.adjoinHostWire outer hostLocals addedLocals)).length) := by
          simpa only [Nat.zero_add] using materialPaths
        rw [materialPaths'] at combinedRoot
        have shifted :=
          (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff addedItems
            materialWire.index.val 0
            ((hostItems.renameWires
              (Region.adjoinHostWire outer hostLocals addedLocals)).length)).mp
            (by simpa using combinedRoot)
        simpa [materialWire, List.length_append, Nat.add_assoc] using shifted
      · have materialChildren :=
          (ItemSeq.childrenCanonical_append _ _).mp canonical.2 |>.2
        exact (ItemSeq.ChildrenCanonical.renameWires_iff addedItems
          (Region.adjoinMaterialWire outer hostLocals addedLocals)).mp
            materialChildren

/-- Adjoining canonical material after a canonical host preserves
canonicality. Host-local roots remain as a subpresentation, while the
material-local roots are shifted past the host block. -/
theorem Region.Canonical.adjoinAt
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals))
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (materialCanonical : material.Canonical) :
    (Region.adjoinAt hostLocals hostItems material).Canonical := by
  cases material with
  | mk addedLocals addedItems =>
      simp only [Region.Canonical] at hostCanonical materialCanonical
      simp only [Region.adjoinAt, Region.Canonical]
      constructor
      · intro combinedIndex
        by_cases inHost : combinedIndex.val < hostLocals.length
        · let hostIndex : Fin hostLocals.length :=
            ⟨combinedIndex.val, inHost⟩
          let hostWire := Var.appendRight outer (Var.ofIndex hostIndex)
          have hostRoot := hostCanonical.1 hostIndex
          have combinedWireIndex :
              outer.length + combinedIndex.val = hostWire.index.val := by
            simp [hostWire, hostIndex]
          rw [combinedWireIndex, ItemSeq.incidencePaths_append]
          rw [ItemSeq.incidencePaths_renameWires_adjoinHost
            hostItems hostWire 0]
          apply RegionPath.RootedTwo.of_sublist
            (List.sublist_append_left _ _)
          simpa [hostWire, hostIndex] using hostRoot
        · have inMaterial :
              combinedIndex.val - hostLocals.length < addedLocals.length := by
            have bound := combinedIndex.isLt
            simp only [List.length_append] at bound
            omega
          let materialIndex : Fin addedLocals.length :=
            ⟨combinedIndex.val - hostLocals.length, inMaterial⟩
          let materialWire := Var.appendRight (outer ++ hostLocals)
            (Var.ofIndex materialIndex)
          have materialRoot := materialCanonical.1 materialIndex
          have combinedWireIndex :
              outer.length + combinedIndex.val = materialWire.index.val := by
            simp [materialWire, materialIndex, List.length_append]
            omega
          rw [combinedWireIndex, ItemSeq.incidencePaths_append]
          have hostEmpty :
              (hostItems.renameWires
                (Region.adjoinHostWire outer hostLocals addedLocals)).incidencePaths
                  materialWire.index.val 0 = [] := by
            apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
            · simp [materialWire]
              omega
            · intro signature wire
              rw [adjoinHost_index]
              have wireBound := wire.index.isLt
              simp only [materialWire, Var.index_appendRight,
                Var.index_ofIndex, List.length_append] at wireBound ⊢
              omega
          rw [hostEmpty, List.nil_append]
          simp only [Nat.zero_add]
          rw [ItemSeq.incidencePaths_renameWires_adjoinMaterial
            addedItems materialWire
              ((hostItems.renameWires
                (Region.adjoinHostWire outer hostLocals addedLocals)).length)]
          have shifted :=
            (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff addedItems
              materialWire.index.val 0
              ((hostItems.renameWires
                (Region.adjoinHostWire outer hostLocals addedLocals)).length)).mpr
              (by simpa [materialWire, materialIndex, List.length_append,
                Nat.add_assoc] using materialRoot)
          simpa only [Nat.zero_add] using shifted
      · apply (ItemSeq.childrenCanonical_append _ _).mpr
        exact ⟨
          (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
            hostItems).mpr hostCanonical.2,
          (ItemSeq.ChildrenCanonical.renameWires_iff addedItems
            (Region.adjoinMaterialWire outer hostLocals addedLocals)).mpr
              materialCanonical.2⟩

/-- The original host presentation occurs unchanged inside an adjoining
extension, at every inherited wire. -/
theorem Region.incidencePaths_adjoinAt_host_sublist
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals))
    (wire : Var outer signature) :
    ((Region.mk hostLocals hostItems).incidencePaths wire.index.val).Sublist
      ((Region.adjoinAt hostLocals hostItems material).incidencePaths
        wire.index.val) := by
  cases material with
  | mk addedLocals addedItems =>
      change (hostItems.incidencePaths wire.index.val 0).Sublist
        (((hostItems.renameWires
            (Region.adjoinHostWire outer hostLocals addedLocals)).append
          (addedItems.renameWires
            (Region.adjoinMaterialWire outer hostLocals addedLocals))).incidencePaths
              wire.index.val 0)
      rw [ItemSeq.incidencePaths_append]
      have renamed := ItemSeq.incidencePaths_renameWires_adjoinHost
        (addedLocals := addedLocals) hostItems
        (wire.appendLeft hostLocals) 0
      rw [show (wire.appendLeft hostLocals).index.val = wire.index.val by simp]
        at renamed
      rw [renamed]
      exact List.sublist_append_left _ _

/-- Appending a zero-local item region to a canonical region preserves
canonicality when the appended items have canonical children. -/
theorem Region.Canonical.conjoinRightItems
    (first : Region outer) (secondItems : ItemSeq outer)
    (firstCanonical : first.Canonical)
    (secondChildren : secondItems.ChildrenCanonical) :
    (first.conjoin (Region.ofItems secondItems)).Canonical := by
  cases first with
  | mk firstLocals firstItems =>
      simp only [Region.ofItems, Region.conjoin, Region.Canonical,
        Region.locals] at firstCanonical ⊢
      constructor
      · intro localIndex
        let sourceIndex : Fin firstLocals.length :=
          ⟨localIndex.val, by
            have bound := localIndex.isLt
            simpa only [List.length_append, List.length_nil, Nat.add_zero]
              using bound⟩
        let sourceWire := Var.appendRight outer (Var.ofIndex sourceIndex)
        have sourceRoot := firstCanonical.1 sourceIndex
        rw [ItemSeq.incidencePaths_append]
        have renamed := ItemSeq.incidencePaths_renameWires_adjoinHost
          (addedLocals := []) firstItems sourceWire 0
        have renamed' :
            (firstItems.renameWires
              (Region.conjoinLeftWire outer firstLocals [])).incidencePaths
                sourceWire.index.val 0 =
              firstItems.incidencePaths sourceWire.index.val 0 := by
          simpa only [Region.adjoinHostWire] using renamed
        have targetIndex : outer.length + localIndex.val =
            sourceWire.index.val := by
          simp [sourceWire, sourceIndex]
        rw [targetIndex, renamed']
        exact RegionPath.RootedTwo.of_sublist
          (List.sublist_append_left _ _) (by
            simpa [sourceWire, sourceIndex] using sourceRoot)
      · apply (ItemSeq.childrenCanonical_append _ _).mpr
        constructor
        · exact (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
            firstItems).mpr firstCanonical.2
        · have secondCanonical :=
            (ItemSeq.ChildrenCanonical.renameWires_iff secondItems
              (WireRenaming.comp
                (Region.conjoinRightWire outer firstLocals [])
                ⟨fun wire => wire.appendLeft []⟩)).mpr secondChildren
          rw [← ItemSeq.renameWires_comp] at secondCanonical
          exact secondCanonical

/-- Canonical material can supply the roots for newly bound host locals when
those inherited material wires are already rooted. -/
theorem Region.Canonical.adjoinAt_of_material_roots
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals))
    (hostChildren : hostItems.ChildrenCanonical)
    (materialCanonical : material.Canonical)
    (hostRoots : ∀ hostIndex : Fin hostLocals.length,
      RegionPath.RootedTwo
        (material.incidencePaths (outer.length + hostIndex.val))) :
    (Region.adjoinAt hostLocals hostItems material).Canonical := by
  cases material with
  | mk addedLocals addedItems =>
      simp only [Region.adjoinAt, Region.Canonical] at materialCanonical ⊢
      constructor
      · intro combinedIndex
        by_cases inHost : combinedIndex.val < hostLocals.length
        · let hostIndex : Fin hostLocals.length :=
            ⟨combinedIndex.val, inHost⟩
          let hostWire := Var.appendRight outer (Var.ofIndex hostIndex)
          let materialHostWire := hostWire.appendLeft addedLocals
          have materialRoot := hostRoots hostIndex
          have shiftedRoot :=
            (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff addedItems
              hostWire.index.val 0
              ((hostItems.renameWires
                (Region.adjoinHostWire outer hostLocals addedLocals)).length)).mpr
              (by simpa [Region.incidencePaths, hostWire, hostIndex] using
                materialRoot)
          have renamedRoot : RegionPath.RootedTwo
              ((addedItems.renameWires
                (Region.adjoinMaterialWire outer hostLocals addedLocals)).incidencePaths
                  hostWire.index.val
                  ((hostItems.renameWires
                    (Region.adjoinHostWire outer hostLocals addedLocals)).length)) := by
            have renamedPaths :=
              ItemSeq.incidencePaths_renameWires_adjoinMaterial addedItems
                materialHostWire
                ((hostItems.renameWires
                  (Region.adjoinHostWire outer hostLocals addedLocals)).length)
            rw [show materialHostWire.index.val = hostWire.index.val by
              simp [materialHostWire]] at renamedPaths
            rw [renamedPaths]
            simpa only [Nat.zero_add] using shiftedRoot
          have inCombined := ItemSeq.incidencePaths_append_right_sublist
            (hostItems.renameWires
              (Region.adjoinHostWire outer hostLocals addedLocals))
            (addedItems.renameWires
              (Region.adjoinMaterialWire outer hostLocals addedLocals))
            hostWire.index.val 0
          have targetIndex : outer.length + combinedIndex.val =
              hostWire.index.val := by
            simp [hostWire, hostIndex]
          rw [targetIndex]
          exact RegionPath.RootedTwo.of_sublist inCombined
            (by simpa only [Nat.zero_add] using renamedRoot)
        · have inMaterial :
              combinedIndex.val - hostLocals.length < addedLocals.length := by
            have bound := combinedIndex.isLt
            simp only [List.length_append] at bound
            omega
          let materialIndex : Fin addedLocals.length :=
            ⟨combinedIndex.val - hostLocals.length, inMaterial⟩
          let materialWire := Var.appendRight (outer ++ hostLocals)
            (Var.ofIndex materialIndex)
          have materialRoot := materialCanonical.1 materialIndex
          have combinedWireIndex :
              outer.length + combinedIndex.val = materialWire.index.val := by
            simp [materialWire, materialIndex, List.length_append]
            omega
          rw [combinedWireIndex, ItemSeq.incidencePaths_append]
          have hostEmpty :
              (hostItems.renameWires
                (Region.adjoinHostWire outer hostLocals addedLocals)).incidencePaths
                  materialWire.index.val 0 = [] := by
            apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
            · simp [materialWire]
              omega
            · intro signature wire
              rw [adjoinHost_index]
              have wireBound := wire.index.isLt
              simp only [materialWire, Var.index_appendRight,
                Var.index_ofIndex, List.length_append] at wireBound ⊢
              omega
          rw [hostEmpty, List.nil_append]
          simp only [Nat.zero_add]
          rw [ItemSeq.incidencePaths_renameWires_adjoinMaterial]
          have shifted :=
            (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff addedItems
              materialWire.index.val 0
              ((hostItems.renameWires
                (Region.adjoinHostWire outer hostLocals addedLocals)).length)).mpr
              (by simpa [materialWire, materialIndex, List.length_append,
                Nat.add_assoc] using materialRoot)
          simpa only [Nat.zero_add] using shifted
      · apply (ItemSeq.childrenCanonical_append _ _).mpr
        exact ⟨
          (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
            hostItems).mpr hostChildren,
          (ItemSeq.ChildrenCanonical.renameWires_iff addedItems
            (Region.adjoinMaterialWire outer hostLocals addedLocals)).mpr
              materialCanonical.2⟩

end VisualProof.Diagram
