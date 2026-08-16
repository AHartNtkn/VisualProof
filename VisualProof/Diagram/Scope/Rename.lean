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

end VisualProof.Diagram
