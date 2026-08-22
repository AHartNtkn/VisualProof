import VisualProof.Diagram.Algebra

namespace VisualProof.Diagram

open VisualProof.Theory

theorem Region.renameWires_conjoin
    (first second : Region sourceWires)
    (rename : WireRenaming sourceWires targetWires) :
    (first.conjoin second).renameWires rename =
      (first.renameWires rename).conjoin (second.renameWires rename) := by
  cases first with
  | mk firstLocals firstItems =>
      cases second with
      | mk secondLocals secondItems =>
          have firstMap : WireRenaming.comp
              (rename.appendRight (firstLocals ++ secondLocals))
              (Region.conjoinLeftWire sourceWires firstLocals secondLocals) =
            WireRenaming.comp
              (Region.conjoinLeftWire targetWires firstLocals secondLocals)
              (rename.appendRight firstLocals) := by
            apply WireRenaming.ext
            intro signature wire
            apply Var.appendCases (left := sourceWires)
              (right := firstLocals)
              (motive := fun wire =>
                WireRenaming.comp
                    (rename.appendRight (firstLocals ++ secondLocals))
                    (Region.conjoinLeftWire sourceWires firstLocals
                      secondLocals) wire =
                  WireRenaming.comp
                    (Region.conjoinLeftWire targetWires firstLocals
                      secondLocals)
                    (rename.appendRight firstLocals) wire)
            · intro inheritedSignature inherited
              simp [WireRenaming.comp, WireRenaming.appendRight,
                Region.conjoinLeftWire]
            · intro localSignature localWire
              simp [WireRenaming.comp, WireRenaming.appendRight,
                Region.conjoinLeftWire]
          have secondMap : WireRenaming.comp
              (rename.appendRight (firstLocals ++ secondLocals))
              (Region.conjoinRightWire sourceWires firstLocals secondLocals) =
            WireRenaming.comp
              (Region.conjoinRightWire targetWires firstLocals secondLocals)
              (rename.appendRight secondLocals) := by
            apply WireRenaming.ext
            intro signature wire
            apply Var.appendCases (left := sourceWires)
              (right := secondLocals)
              (motive := fun wire =>
                WireRenaming.comp
                    (rename.appendRight (firstLocals ++ secondLocals))
                    (Region.conjoinRightWire sourceWires firstLocals
                      secondLocals) wire =
                  WireRenaming.comp
                    (Region.conjoinRightWire targetWires firstLocals
                      secondLocals)
                    (rename.appendRight secondLocals) wire)
            · intro inheritedSignature inherited
              simp [WireRenaming.comp, WireRenaming.appendRight,
                Region.conjoinRightWire]
            · intro localSignature localWire
              simp [WireRenaming.comp, WireRenaming.appendRight,
                Region.conjoinRightWire]
          simp only [Region.conjoin, Region.renameWires,
            ItemSeq.renameWires_append, ItemSeq.renameWires_comp]
          rw [firstMap, secondMap]

noncomputable def RegionIso.renameWiresConjoin
    (first second : Region sourceWires)
    (rename : WireRenaming sourceWires targetWires) :
    RegionIso (WireEquiv.refl targetWires)
      ((first.conjoin second).renameWires rename)
      ((first.renameWires rename).conjoin (second.renameWires rename)) := by
  rw [Region.renameWires_conjoin]
  exact RegionIso.refl _

noncomputable def RegionIso.renameWiresComp
    (region : Region sourceWires)
    (first : WireRenaming sourceWires middleWires)
    (second : WireRenaming middleWires targetWires) :
    RegionIso (WireEquiv.refl targetWires)
      ((region.renameWires first).renameWires second)
      (region.renameWires (WireRenaming.comp second first)) := by
  rw [Region.renameWires_comp]
  exact RegionIso.refl _

def WireEquiv.adjoinMaterialAssoc
    (outer hostLocals addedLocals : List Sig) :
    WireEquiv ((outer ++ hostLocals) ++ addedLocals)
      (outer ++ (hostLocals ++ addedLocals)) where
  toRenaming := Region.adjoinMaterialWire outer hostLocals addedLocals
  invRenaming := ⟨Var.appendMap
    (fun wire => (wire.appendLeft hostLocals).appendLeft addedLocals)
    (fun wire => Var.appendMap
      (fun hostWire =>
        (Var.appendRight outer hostWire).appendLeft addedLocals)
      (fun addedWire => Var.appendRight (outer ++ hostLocals) addedWire)
      wire)⟩
  left_inv := by
    intro signature wire
    apply Var.appendCases (left := outer ++ hostLocals)
      (right := addedLocals)
      (motive := fun wire =>
        Var.appendMap
          (fun wire => (wire.appendLeft hostLocals).appendLeft addedLocals)
          (fun wire => Var.appendMap
            (fun hostWire =>
              (Var.appendRight outer hostWire).appendLeft addedLocals)
            (fun addedWire =>
              Var.appendRight (outer ++ hostLocals) addedWire)
            wire)
          (Region.adjoinMaterialWire outer hostLocals addedLocals wire) =
            wire)
    · intro inheritedSignature inherited
      apply Var.appendCases (left := outer) (right := hostLocals)
        (motive := fun inherited =>
          Var.appendMap
            (fun wire => (wire.appendLeft hostLocals).appendLeft addedLocals)
            (fun wire => Var.appendMap
              (fun hostWire =>
                (Var.appendRight outer hostWire).appendLeft addedLocals)
              (fun addedWire =>
                Var.appendRight (outer ++ hostLocals) addedWire)
              wire)
            (Region.adjoinMaterialWire outer hostLocals addedLocals
              (inherited.appendLeft addedLocals)) =
                inherited.appendLeft addedLocals)
      · intro outerSignature outerWire
        simp [Region.adjoinMaterialWire]
      · intro hostSignature hostWire
        simp [Region.adjoinMaterialWire]
    · intro addedSignature addedWire
      simp [Region.adjoinMaterialWire]
  right_inv := by
    intro signature wire
    apply Var.appendCases (left := outer)
      (right := hostLocals ++ addedLocals)
      (motive := fun wire =>
        Region.adjoinMaterialWire outer hostLocals addedLocals
          (Var.appendMap
            (fun wire => (wire.appendLeft hostLocals).appendLeft addedLocals)
            (fun wire => Var.appendMap
              (fun hostWire =>
                (Var.appendRight outer hostWire).appendLeft addedLocals)
              (fun addedWire =>
                Var.appendRight (outer ++ hostLocals) addedWire)
              wire)
            wire) = wire)
    · intro outerSignature outerWire
      simp [Region.adjoinMaterialWire]
    · intro localSignature localWire
      apply Var.appendCases (left := hostLocals) (right := addedLocals)
        (motive := fun localWire =>
          Region.adjoinMaterialWire outer hostLocals addedLocals
            (Var.appendMap
              (fun wire => (wire.appendLeft hostLocals).appendLeft addedLocals)
              (fun wire => Var.appendMap
                (fun hostWire =>
                  (Var.appendRight outer hostWire).appendLeft addedLocals)
                (fun addedWire =>
                  Var.appendRight (outer ++ hostLocals) addedWire)
                wire)
              (Var.appendRight outer localWire)) =
                Var.appendRight outer localWire)
      · intro hostSignature hostWire
        simp [Region.adjoinMaterialWire]
      · intro addedSignature addedWire
        simp [Region.adjoinMaterialWire]

/-- Lift a material presentation through a retained host prefix. -/
noncomputable def RegionIso.adjoinAt
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    {before after : Region (outer ++ hostLocals)}
    (material : RegionIso (WireEquiv.refl (outer ++ hostLocals))
      before after) :
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt hostLocals hostItems before)
      (Region.adjoinAt hostLocals hostItems after) := by
  cases material with
  | @mk _ _ sourceLocals targetLocals _ sourceItems targetItems
      localIso itemIso =>
      let localAmbient := (WireEquiv.refl hostLocals).append localIso
      let ambient := (WireEquiv.refl outer).append localAmbient
      let sourceAssoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
        sourceLocals
      let targetAssoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
        targetLocals
      have sourceBack : ItemSeqIso sourceAssoc.symm
          (sourceItems.renameWires
            (Region.adjoinMaterialWire outer hostLocals sourceLocals))
          sourceItems := by
        let raw := ItemSeqIso.renameWires sourceItems
          (Region.adjoinMaterialWire outer hostLocals sourceLocals)
          WireRenaming.id sourceAssoc.symm (by
            intro signature wire
            exact sourceAssoc.left_inv wire)
        simpa only [ItemSeq.renameWires_id] using raw
      have targetForward : ItemSeqIso targetAssoc targetItems
          (targetItems.renameWires
            (Region.adjoinMaterialWire outer hostLocals targetLocals)) := by
        let raw := ItemSeqIso.renameWires targetItems WireRenaming.id
          (Region.adjoinMaterialWire outer hostLocals targetLocals)
          targetAssoc (by
            intro signature wire
            rfl)
        simpa only [ItemSeq.renameWires_id] using raw
      let materialItems := (sourceBack.trans itemIso).trans targetForward
      have assocCommutes : ∀ {signature}
          (wire : Var ((outer ++ hostLocals) ++ sourceLocals) signature),
          targetAssoc
              (((WireEquiv.refl (outer ++ hostLocals)).append localIso) wire) =
            ambient (sourceAssoc wire) := by
        intro signature wire
        apply Var.appendCases (left := outer ++ hostLocals)
          (right := sourceLocals)
          (motive := fun wire =>
            targetAssoc
                (((WireEquiv.refl (outer ++ hostLocals)).append localIso)
                  wire) =
              ambient (sourceAssoc wire))
        · intro inheritedSignature inherited
          apply Var.appendCases (left := outer) (right := hostLocals)
            (motive := fun inherited =>
              targetAssoc
                  (((WireEquiv.refl (outer ++ hostLocals)).append localIso)
                    (inherited.appendLeft sourceLocals)) =
                ambient (sourceAssoc
                  (inherited.appendLeft sourceLocals)))
          · intro outerSignature outerWire
            simp [sourceAssoc, targetAssoc,
              WireEquiv.adjoinMaterialAssoc, ambient, localAmbient,
              Region.adjoinMaterialWire]
          · intro hostSignature hostWire
            simp [sourceAssoc, targetAssoc,
              WireEquiv.adjoinMaterialAssoc, ambient, localAmbient,
              Region.adjoinMaterialWire]
        · intro localSignature localWire
          simp [sourceAssoc, targetAssoc, WireEquiv.adjoinMaterialAssoc,
            ambient, localAmbient, Region.adjoinMaterialWire]
      have materialAmbient :
          (sourceAssoc.symm.trans
            ((WireEquiv.refl (outer ++ hostLocals)).append localIso)).trans
              targetAssoc = ambient := by
        apply WireEquiv.ext
        intro signature wire
        let original := sourceAssoc.symm wire
        calc
          ((sourceAssoc.symm.trans
              ((WireEquiv.refl (outer ++ hostLocals)).append localIso)).trans
                targetAssoc) wire =
              targetAssoc
                (((WireEquiv.refl (outer ++ hostLocals)).append localIso)
                  original) := rfl
          _ = ambient (sourceAssoc original) := assocCommutes original
          _ = ambient wire := congrArg (fun mapped => ambient mapped)
            (sourceAssoc.right_inv wire)
      have materialItems' : ItemSeqIso ambient
          (sourceItems.renameWires
            (Region.adjoinMaterialWire outer hostLocals sourceLocals))
          (targetItems.renameWires
            (Region.adjoinMaterialWire outer hostLocals targetLocals)) :=
        materialItems.castAmbient materialAmbient
      have hostIso : ItemSeqIso ambient
          (hostItems.renameWires
            (Region.adjoinHostWire outer hostLocals sourceLocals))
          (hostItems.renameWires
            (Region.adjoinHostWire outer hostLocals targetLocals)) := by
        apply ItemSeqIso.renameWires hostItems
          (Region.adjoinHostWire outer hostLocals sourceLocals)
          (Region.adjoinHostWire outer hostLocals targetLocals) ambient
        intro signature wire
        apply Var.appendCases (left := outer) (right := hostLocals)
          (motive := fun wire =>
            ((WireEquiv.refl outer).append
              ((WireEquiv.refl hostLocals).append localIso))
                (Region.adjoinHostWire outer hostLocals sourceLocals wire) =
              Region.adjoinHostWire outer hostLocals targetLocals wire)
        · intro inheritedSignature inherited
          apply Var.eq_of_index_eq
          apply Fin.ext
          simp [Region.adjoinHostWire, Region.conjoinLeftWire]
        · intro localSignature localWire
          apply Var.eq_of_index_eq
          apply Fin.ext
          simp [Region.adjoinHostWire, Region.conjoinLeftWire]
      refine .mk localAmbient ?_
      simpa only [ambient] using ItemSeqIso.append hostIso materialItems'

private theorem WireEquiv.refl_append_ofEq_index_val
    (equality : sourceLocals = targetLocals)
    (wire : Var (outer ++ sourceLocals) signature) :
    (((WireEquiv.refl outer).append (WireEquiv.ofEq equality)) wire).index.val =
      wire.index.val := by
  cases equality
  change
    (((WireEquiv.refl outer).append (WireEquiv.refl sourceLocals)) wire).index.val =
      wire.index.val
  rw [WireEquiv.append_refl]
  rfl

/-- Reassociate exactly one nested `Region.adjoinAt`. -/
noncomputable def RegionIso.adjoinAtAssoc
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (innerLocals : List Sig)
    (innerItems : ItemSeq ((outer ++ hostLocals) ++ innerLocals))
    (material : Region ((outer ++ hostLocals) ++ innerLocals)) :
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt (hostLocals ++ innerLocals)
        (Region.extendHostItems hostLocals hostItems
          (.mk innerLocals innerItems))
        (material.renameWires
          (Region.adjoinMaterialWire outer hostLocals innerLocals)))
      (Region.adjoinAt hostLocals hostItems
        (Region.adjoinAt innerLocals innerItems material)) := by
  cases material with
  | mk materialLocals materialItems =>
      let sourcePrefix := Region.adjoinHostWire outer
        (hostLocals ++ innerLocals) materialLocals
      let sourceHost := WireRenaming.comp sourcePrefix
        (Region.adjoinHostWire outer hostLocals innerLocals)
      let sourceInner := WireRenaming.comp sourcePrefix
        (Region.adjoinMaterialWire outer hostLocals innerLocals)
      let sourceMaterial := WireRenaming.comp
        (Region.adjoinMaterialWire outer (hostLocals ++ innerLocals)
          materialLocals)
        ((Region.adjoinMaterialWire outer hostLocals innerLocals).appendRight
          materialLocals)
      let targetPrefix := Region.adjoinMaterialWire outer hostLocals
        (innerLocals ++ materialLocals)
      let targetHost := Region.adjoinHostWire outer hostLocals
        (innerLocals ++ materialLocals)
      let targetInner := WireRenaming.comp targetPrefix
        (Region.adjoinHostWire (outer ++ hostLocals) innerLocals
          materialLocals)
      let targetMaterial := WireRenaming.comp targetPrefix
        (Region.adjoinMaterialWire (outer ++ hostLocals) innerLocals
          materialLocals)
      let localsIso := WireEquiv.ofEq
        (List.append_assoc hostLocals innerLocals materialLocals)
      let ambient := (WireEquiv.refl outer).append localsIso
      have ambientIndex : ∀ {signature}
          (wire : Var (outer ++ ((hostLocals ++ innerLocals) ++
            materialLocals)) signature),
          (ambient wire).index.val = wire.index.val := by
        intro signature wire
        exact WireEquiv.refl_append_ofEq_index_val
          (List.append_assoc hostLocals innerLocals materialLocals) wire
      have hostCommutes : ∀ {signature}
          (wire : Var (outer ++ hostLocals) signature),
          ambient (sourceHost wire) = targetHost wire := by
        intro signature wire
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [ambientIndex]
        simp only [sourceHost, sourcePrefix, targetHost, WireRenaming.comp,
          Region.adjoinHostWire_index_val]
      have innerCommutes : ∀ {signature}
          (wire : Var ((outer ++ hostLocals) ++ innerLocals) signature),
          ambient (sourceInner wire) = targetInner wire := by
        intro signature wire
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [ambientIndex]
        simp only [sourceInner, sourcePrefix, targetInner, targetPrefix,
          WireRenaming.comp, Region.adjoinHostWire_index_val,
          Region.adjoinMaterialWire_index_val]
      have appendedMaterialIndex : ∀ {signature}
          (wire : Var (((outer ++ hostLocals) ++ innerLocals) ++
            materialLocals) signature),
          (((Region.adjoinMaterialWire outer hostLocals innerLocals).appendRight
            materialLocals) wire).index.val = wire.index.val := by
        intro signature wire
        apply Var.appendCases
          (left := (outer ++ hostLocals) ++ innerLocals)
          (right := materialLocals)
          (motive := fun wire =>
            (((Region.adjoinMaterialWire outer hostLocals
              innerLocals).appendRight materialLocals) wire).index.val =
                wire.index.val)
        · intro inheritedSignature inherited
          simp [WireRenaming.appendRight]
        · intro localSignature localWire
          simp [WireRenaming.appendRight]
      have materialCommutes : ∀ {signature}
          (wire : Var (((outer ++ hostLocals) ++ innerLocals) ++
            materialLocals) signature),
          ambient (sourceMaterial wire) = targetMaterial wire := by
        intro signature wire
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [ambientIndex]
        simp only [sourceMaterial, targetMaterial, targetPrefix,
          WireRenaming.comp, Region.adjoinMaterialWire_index_val]
        exact appendedMaterialIndex wire
      let hostIso := ItemSeqIso.renameWires hostItems sourceHost targetHost
        ambient hostCommutes
      let innerIso := ItemSeqIso.renameWires innerItems sourceInner targetInner
        ambient innerCommutes
      let materialIso := ItemSeqIso.renameWires materialItems sourceMaterial
        targetMaterial ambient materialCommutes
      refine .mk localsIso ?_
      simpa only [Region.adjoinAt, Region.renameWires, Region.locals,
        Region.items, Region.extendHostItems, ItemSeq.renameWires_append,
        ItemSeq.renameWires_comp, ItemSeq.append_assoc, sourcePrefix,
        sourceHost, sourceInner, sourceMaterial, targetPrefix, targetHost,
        targetInner, targetMaterial, ambient] using
        ItemSeqIso.append hostIso (ItemSeqIso.append innerIso materialIso)

/-- Flatten a leading material block into the retained host. -/
noncomputable def RegionIso.adjoinAtConjoinLeft
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (first second : Region (outer ++ hostLocals)) :
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt hostLocals hostItems (first.conjoin second))
      (Region.adjoinAt (hostLocals ++ first.locals)
        (Region.extendHostItems hostLocals hostItems first)
        (second.renameWires
          (Region.adjoinHostWire outer hostLocals first.locals))) := by
  cases first with
  | mk firstLocals firstItems =>
      cases second with
      | mk secondLocals secondItems =>
          let sourceHost := Region.adjoinHostWire outer hostLocals
            (firstLocals ++ secondLocals)
          let sourceFirst := WireRenaming.comp
            (Region.adjoinMaterialWire outer hostLocals
              (firstLocals ++ secondLocals))
            (Region.conjoinLeftWire (outer ++ hostLocals) firstLocals
              secondLocals)
          let sourceSecond := WireRenaming.comp
            (Region.adjoinMaterialWire outer hostLocals
              (firstLocals ++ secondLocals))
            (Region.conjoinRightWire (outer ++ hostLocals) firstLocals
              secondLocals)
          let targetPrefix := Region.adjoinHostWire outer
            (hostLocals ++ firstLocals) secondLocals
          let targetHost := WireRenaming.comp targetPrefix
            (Region.adjoinHostWire outer hostLocals firstLocals)
          let targetFirst := WireRenaming.comp targetPrefix
            (Region.adjoinMaterialWire outer hostLocals firstLocals)
          let targetSecond := WireRenaming.comp
            (Region.adjoinMaterialWire outer
              (hostLocals ++ firstLocals) secondLocals)
            ((Region.adjoinHostWire outer hostLocals firstLocals).appendRight
              secondLocals)
          let localsIso := WireEquiv.ofEq
            (List.append_assoc hostLocals firstLocals secondLocals).symm
          let ambient := (WireEquiv.refl outer).append localsIso
          have maps :
              (∀ {signature} (wire : Var (outer ++ hostLocals) signature),
                ambient (sourceHost wire) = targetHost wire) ∧
              (∀ {signature}
                (wire : Var ((outer ++ hostLocals) ++ firstLocals)
                  signature),
                ambient (sourceFirst wire) = targetFirst wire) ∧
              (∀ {signature}
                (wire : Var ((outer ++ hostLocals) ++ secondLocals)
                  signature),
                ambient (sourceSecond wire) = targetSecond wire) := by
            constructor
            · intro signature wire
              apply Var.appendCases (left := outer) (right := hostLocals)
                (motive := fun wire =>
                  ambient (sourceHost wire) = targetHost wire)
              · intro inheritedSignature inherited
                apply Var.eq_of_index_eq
                apply Fin.ext
                simp [ambient, localsIso, sourceHost, targetHost,
                  targetPrefix, WireRenaming.comp,
                  Region.adjoinHostWire, Region.conjoinLeftWire]
              · intro localSignature localWire
                apply Var.eq_of_index_eq
                apply Fin.ext
                simp [ambient, localsIso, sourceHost, targetHost,
                  targetPrefix, WireRenaming.comp,
                  Region.adjoinHostWire, Region.conjoinLeftWire]
            constructor
            · intro signature wire
              apply Var.appendCases (left := outer ++ hostLocals)
                (right := firstLocals)
                (motive := fun wire =>
                  ambient (sourceFirst wire) = targetFirst wire)
              · intro inheritedSignature inherited
                apply Var.appendCases (left := outer) (right := hostLocals)
                  (motive := fun inherited =>
                    ambient (sourceFirst
                        (inherited.appendLeft firstLocals)) =
                      targetFirst (inherited.appendLeft firstLocals))
                · intro outerSignature outerWire
                  apply Var.eq_of_index_eq
                  apply Fin.ext
                  simp [ambient, localsIso, sourceFirst, targetFirst,
                    targetPrefix, WireRenaming.comp,
                    Region.adjoinMaterialWire, Region.adjoinHostWire,
                    Region.conjoinLeftWire]
                · intro hostSignature hostWire
                  apply Var.eq_of_index_eq
                  apply Fin.ext
                  simp [ambient, localsIso, sourceFirst, targetFirst,
                    targetPrefix, WireRenaming.comp,
                    Region.adjoinMaterialWire, Region.adjoinHostWire,
                    Region.conjoinLeftWire]
              · intro localSignature localWire
                apply Var.eq_of_index_eq
                apply Fin.ext
                simp [ambient, localsIso, sourceFirst, targetFirst,
                  targetPrefix, WireRenaming.comp,
                  Region.adjoinMaterialWire, Region.adjoinHostWire,
                  Region.conjoinLeftWire]
            · intro signature wire
              apply Var.appendCases (left := outer ++ hostLocals)
                (right := secondLocals)
                (motive := fun wire =>
                  ambient (sourceSecond wire) = targetSecond wire)
              · intro inheritedSignature inherited
                apply Var.appendCases (left := outer) (right := hostLocals)
                  (motive := fun inherited =>
                    ambient (sourceSecond
                        (inherited.appendLeft secondLocals)) =
                      targetSecond (inherited.appendLeft secondLocals))
                · intro outerSignature outerWire
                  apply Var.eq_of_index_eq
                  apply Fin.ext
                  simp [ambient, localsIso, sourceSecond, targetSecond,
                    WireRenaming.comp, WireRenaming.appendRight,
                    Region.adjoinMaterialWire, Region.adjoinHostWire,
                    Region.conjoinLeftWire, Region.conjoinRightWire]
                · intro hostSignature hostWire
                  apply Var.eq_of_index_eq
                  apply Fin.ext
                  simp [ambient, localsIso, sourceSecond, targetSecond,
                    WireRenaming.comp, WireRenaming.appendRight,
                    Region.adjoinMaterialWire, Region.adjoinHostWire,
                    Region.conjoinLeftWire, Region.conjoinRightWire]
              · intro localSignature localWire
                apply Var.eq_of_index_eq
                apply Fin.ext
                simp [ambient, localsIso, sourceSecond, targetSecond,
                  WireRenaming.comp, WireRenaming.appendRight,
                  Region.adjoinMaterialWire, Region.adjoinHostWire,
                  Region.conjoinLeftWire, Region.conjoinRightWire]
                omega
          let hostIso := ItemSeqIso.renameWires hostItems sourceHost
            targetHost ambient maps.1
          let firstIso := ItemSeqIso.renameWires firstItems sourceFirst
            targetFirst ambient maps.2.1
          let secondIso := ItemSeqIso.renameWires secondItems sourceSecond
            targetSecond ambient maps.2.2
          let combined := ItemSeqIso.append
            (ItemSeqIso.append hostIso firstIso) secondIso
          refine .mk localsIso ?_
          simpa only [Region.adjoinAt, Region.conjoin, Region.renameWires,
            Region.locals, Region.items, ItemSeq.renameWires_append,
            ItemSeq.renameWires_comp, ItemSeq.append_assoc,
            Region.extendHostItems, sourceHost, sourceFirst, sourceSecond,
            targetPrefix, targetHost, targetFirst, targetSecond, ambient]
            using combined

/-- Conjunction is commutative up to region presentation. -/
noncomputable def RegionIso.conjoinComm
    (left right : Region outer) :
    RegionIso (WireEquiv.refl outer) (left.conjoin right)
      (right.conjoin left) := by
  cases left with
  | mk leftLocals leftItems =>
      cases right with
      | mk rightLocals rightItems =>
          let localSwap := WireEquiv.swap leftLocals rightLocals
          let ambient := (WireEquiv.refl outer).append localSwap
          let sourceLeft := Region.conjoinLeftWire outer leftLocals rightLocals
          let sourceRight :=
            Region.conjoinRightWire outer leftLocals rightLocals
          let targetLeft :=
            Region.conjoinRightWire outer rightLocals leftLocals
          let targetRight :=
            Region.conjoinLeftWire outer rightLocals leftLocals
          have leftCommutes : ∀ {signature}
              (wire : Var (outer ++ leftLocals) signature),
              ambient (sourceLeft wire) = targetLeft wire := by
            intro signature wire
            apply Var.appendCases (left := outer) (right := leftLocals)
              (motive := fun wire =>
                ambient (sourceLeft wire) = targetLeft wire)
            · intro inheritedSignature inherited
              dsimp only [ambient, sourceLeft, targetLeft]
              simp only [Region.conjoinLeftWire,
                Region.conjoinRightWire, Var.appendMap_left]
              change ((WireEquiv.refl outer).append localSwap)
                (inherited.appendLeft (leftLocals ++ rightLocals)) =
                  inherited.appendLeft (rightLocals ++ leftLocals)
              rw [WireEquiv.append_apply_left]
              rfl
            · intro localSignature localWire
              dsimp only [ambient, sourceLeft, targetLeft]
              simp only [Region.conjoinLeftWire,
                Region.conjoinRightWire, Var.appendMap_right]
              change ((WireEquiv.refl outer).append localSwap)
                (Var.appendRight outer
                  (localWire.appendLeft rightLocals)) =
                    Var.appendRight outer
                      (Var.appendRight rightLocals localWire)
              rw [WireEquiv.append_apply_right]
              dsimp only [localSwap, WireEquiv.swap]
              rw [Var.appendMap_left]
          have rightCommutes : ∀ {signature}
              (wire : Var (outer ++ rightLocals) signature),
              ambient (sourceRight wire) = targetRight wire := by
            intro signature wire
            apply Var.appendCases (left := outer) (right := rightLocals)
              (motive := fun wire =>
                ambient (sourceRight wire) = targetRight wire)
            · intro inheritedSignature inherited
              dsimp only [ambient, sourceRight, targetRight]
              simp only [Region.conjoinLeftWire,
                Region.conjoinRightWire, Var.appendMap_left]
              change ((WireEquiv.refl outer).append localSwap)
                (inherited.appendLeft (leftLocals ++ rightLocals)) =
                  inherited.appendLeft (rightLocals ++ leftLocals)
              rw [WireEquiv.append_apply_left]
              rfl
            · intro localSignature localWire
              dsimp only [ambient, sourceRight, targetRight]
              simp only [Region.conjoinLeftWire,
                Region.conjoinRightWire, Var.appendMap_right]
              change ((WireEquiv.refl outer).append localSwap)
                (Var.appendRight outer
                  (Var.appendRight leftLocals localWire)) =
                    Var.appendRight outer
                      (localWire.appendLeft leftLocals)
              rw [WireEquiv.append_apply_right]
              dsimp only [localSwap, WireEquiv.swap]
              rw [Var.appendMap_right]
          let leftIso := ItemSeqIso.renameWires leftItems sourceLeft
            targetLeft ambient leftCommutes
          let rightIso := ItemSeqIso.renameWires rightItems sourceRight
            targetRight ambient rightCommutes
          let reordered := (ItemSeqIso.append leftIso rightIso).trans
            (ItemSeqIso.swapAppend
              (leftItems.renameWires targetLeft)
              (rightItems.renameWires targetRight))
          refine .mk localSwap ?_
          exact reordered.castAmbient (WireEquiv.trans_refl ambient)

/-- Presentation with a host suffix placed after already-adjoined material. -/
def Region.appendAdjoinedHostSuffix
    (hostLocals : List Sig) (hostItems suffix : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) : Region outer :=
  match material with
  | .mk materialLocals materialItems =>
      let hostRename := Region.adjoinHostWire outer hostLocals materialLocals
      let materialRename :=
        Region.adjoinMaterialWire outer hostLocals materialLocals
      .mk (hostLocals ++ materialLocals)
        (((hostItems.renameWires hostRename).append
          (materialItems.renameWires materialRename)).append
            (suffix.renameWires hostRename))

/-- Move a host suffix before already-adjoined material. -/
noncomputable def RegionIso.adjoinAtMoveHostSuffix
    (hostLocals : List Sig) (hostItems suffix : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) :
    RegionIso (WireEquiv.refl outer)
      (Region.appendAdjoinedHostSuffix hostLocals hostItems suffix material)
      (Region.adjoinAt hostLocals (hostItems.append suffix) material) := by
  cases material with
  | mk materialLocals materialItems =>
      let hostRename := Region.adjoinHostWire outer hostLocals materialLocals
      let materialRename :=
        Region.adjoinMaterialWire outer hostLocals materialLocals
      let host := hostItems.renameWires hostRename
      let material := materialItems.renameWires materialRename
      let suffixItems := suffix.renameWires hostRename
      let reordered : ItemSeqIso
          (WireEquiv.refl (outer ++ (hostLocals ++ materialLocals)))
          ((host.append material).append suffixItems)
          ((host.append suffixItems).append material) := by
        let moved := ItemSeqIso.append (ItemSeqIso.refl host)
          (ItemSeqIso.swapAppend material suffixItems)
        simpa only [ItemSeq.append_assoc] using moved
      refine .mk (WireEquiv.refl (hostLocals ++ materialLocals)) ?_
      simpa only [Region.adjoinAt, Region.locals, Region.items,
        ItemSeq.renameWires_append, hostRename, materialRename, host,
        material, suffixItems] using
        reordered.castAmbient
          (WireEquiv.append_refl outer
            (hostLocals ++ materialLocals)).symm

theorem Region.renameWires_adjoinAt_nil
    {common locals outer : List Sig}
    (child : Region (common ++ locals))
    (rename : WireRenaming common outer) :
    (Region.adjoinAt locals .nil child).renameWires rename =
      Region.adjoinAt locals .nil
        (child.renameWires (rename.appendRight locals)) := by
  cases child with
  | mk childLocals childItems =>
      simp only [Region.renameWires, Region.adjoinAt, ItemSeq.renameWires,
        ItemSeq.nil_append]
      rw [ItemSeq.renameWires_comp, ItemSeq.renameWires_comp]
      have mapEq :
          WireRenaming.comp (rename.appendRight (locals ++ childLocals))
              (Region.adjoinMaterialWire common locals childLocals) =
            WireRenaming.comp
              (Region.adjoinMaterialWire outer locals childLocals)
              ((rename.appendRight locals).appendRight childLocals) := by
        apply WireRenaming.ext
        intro signature wire
        apply Var.appendCases (left := common ++ locals)
          (right := childLocals)
          (motive := fun wire =>
            WireRenaming.comp (rename.appendRight (locals ++ childLocals))
                (Region.adjoinMaterialWire common locals childLocals) wire =
              WireRenaming.comp
                (Region.adjoinMaterialWire outer locals childLocals)
                ((rename.appendRight locals).appendRight childLocals) wire)
        · intro inheritedSignature inherited
          apply Var.appendCases (left := common) (right := locals)
            (motive := fun inherited =>
              WireRenaming.comp (rename.appendRight (locals ++ childLocals))
                  (Region.adjoinMaterialWire common locals childLocals)
                  (inherited.appendLeft childLocals) =
                WireRenaming.comp
                  (Region.adjoinMaterialWire outer locals childLocals)
                  ((rename.appendRight locals).appendRight childLocals)
                  (inherited.appendLeft childLocals))
          · intro inheritedSignature inherited
            simp [WireRenaming.comp, WireRenaming.appendRight,
              Region.adjoinMaterialWire]
          · intro localSignature localWire
            simp [WireRenaming.comp, WireRenaming.appendRight,
              Region.adjoinMaterialWire]
        · intro childSignature childWire
          simp [WireRenaming.comp, WireRenaming.appendRight,
            Region.adjoinMaterialWire]
      rw [mapEq]

noncomputable def RegionIso.renameWiresAdjoinAtNil
    {common locals outer : List Sig}
    (child : Region (common ++ locals))
    (rename : WireRenaming common outer) :
    RegionIso (WireEquiv.refl outer)
      ((Region.adjoinAt locals .nil child).renameWires rename)
      (Region.adjoinAt locals .nil
        (child.renameWires (rename.appendRight locals))) := by
  rw [Region.renameWires_adjoinAt_nil]
  exact RegionIso.refl _

theorem Region.singleton_renameWires
    (item : Item sourceWires)
    (rename : WireRenaming sourceWires targetWires) :
    (Region.singleton item).renameWires rename =
      Region.singleton (item.renameWires rename) := by
  simp only [Region.singleton, Region.ofItems, Region.renameWires,
    ItemSeq.renameWires]
  congr 2
  rw [Item.renameWires_comp item
    (⟨fun wire => wire.appendLeft []⟩ :
      WireRenaming sourceWires (sourceWires ++ []))
    (rename.appendRight [])]
  calc
    item.renameWires
        (WireRenaming.comp (rename.appendRight [])
          ⟨fun wire => wire.appendLeft []⟩) =
      item.renameWires
        (WireRenaming.comp ⟨fun wire => wire.appendLeft []⟩ rename) := by
          have mapEq :
              WireRenaming.comp (rename.appendRight [])
                  (⟨fun wire => wire.appendLeft []⟩ :
                    WireRenaming sourceWires (sourceWires ++ [])) =
                WireRenaming.comp
                  (⟨fun wire => wire.appendLeft []⟩ :
                    WireRenaming targetWires (targetWires ++ [])) rename := by
            apply WireRenaming.ext
            intro signature wire
            simp [WireRenaming.comp, WireRenaming.appendRight]
          exact congrArg
            (fun map : WireRenaming sourceWires (targetWires ++ []) =>
              item.renameWires map) mapEq
    _ = (item.renameWires rename).renameWires
        ⟨fun wire => wire.appendLeft []⟩ := by
          rw [Item.renameWires_comp]

noncomputable def RegionIso.adjoinAtSingleton
    (locals : List Sig) (items : ItemSeq (outer ++ locals))
    (item : Item (outer ++ locals)) :
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt locals items (Region.singleton item))
      (Region.mk locals (items.append (.cons item .nil))) := by
  let localIso : WireEquiv (locals ++ []) locals :=
    WireEquiv.ofEq (List.append_nil locals)
  let ambient := (WireEquiv.refl outer).append localIso
  let sourceHost := Region.adjoinHostWire outer locals []
  have hostCommutes : ∀ {signature}
      (wire : Var (outer ++ locals) signature),
      ambient (sourceHost wire) = wire := by
    intro signature wire
    apply Var.appendCases (left := outer) (right := locals)
      (motive := fun wire => ambient (sourceHost wire) = wire)
    · intro inheritedSignature inherited
      simp [ambient, localIso, sourceHost, Region.adjoinHostWire,
        Region.conjoinLeftWire]
    · intro localSignature localWire
      apply Var.eq_of_index_eq
      apply Fin.ext
      simp [ambient, localIso, sourceHost, Region.adjoinHostWire,
        Region.conjoinLeftWire]
  let hostIso := ItemSeqIso.renameWires items sourceHost WireRenaming.id
    ambient hostCommutes
  let appendNil : WireRenaming (outer ++ locals)
      ((outer ++ locals) ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  let sourceItem := WireRenaming.comp
    (Region.adjoinMaterialWire outer locals []) appendNil
  have itemCommutes : ∀ {signature}
      (wire : Var (outer ++ locals) signature),
      ambient (sourceItem wire) = wire := by
    intro signature wire
    apply Var.appendCases (left := outer) (right := locals)
      (motive := fun wire => ambient (sourceItem wire) = wire)
    · intro inheritedSignature inherited
      simp [ambient, localIso, sourceItem, appendNil, WireRenaming.comp,
        Region.adjoinMaterialWire]
    · intro localSignature localWire
      apply Var.eq_of_index_eq
      apply Fin.ext
      simp [ambient, localIso, sourceItem, appendNil, WireRenaming.comp,
        Region.adjoinMaterialWire]
  let itemIso := ItemIso.renameWires item sourceItem WireRenaming.id
    ambient itemCommutes
  let nilIso : ItemSeqIso ambient
      (.nil : ItemSeq (outer ++ (locals ++ [])))
      (.nil : ItemSeq (outer ++ locals)) :=
    .permute (FiniteEquiv.refl _) fun index => Fin.elim0 index
  let combined := ItemSeqIso.append hostIso
    (ItemSeqIso.cons itemIso nilIso)
  refine .mk localIso ?_
  simpa only [Region.adjoinAt, Region.singleton, Region.ofItems,
    ItemSeq.renameWires, ItemSeq.renameWires_id,
    Item.renameWires_comp, Item.renameWires_id,
    sourceHost, sourceItem, appendNil, ambient] using combined

end VisualProof.Diagram
