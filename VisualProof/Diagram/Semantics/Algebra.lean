import VisualProof.Diagram.Algebra
import VisualProof.Diagram.Semantics.Context

namespace VisualProof.Diagram

open VisualProof
open Theory

private theorem renameAppendValues
    (renameWires : WireRenaming source target)
    (targetEnv : Values model target) (localEnv : Values model locals) :
    Values.rename (renameWires.appendRight locals)
        (targetEnv.append localEnv) =
      (Values.rename renameWires targetEnv).append localEnv := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (Values.rename (renameWires.appendRight locals)
          (targetEnv.append localEnv)).lookup wire =
        ((Values.rename renameWires targetEnv).append localEnv).lookup wire)
  · intro signature inherited
    simp [WireRenaming.appendRight]
  · intro signature localWire
    simp [WireRenaming.appendRight]

mutual
  theorem denoteRegion_renameWires
      (model : Model) (renameWires : WireRenaming source target)
      (targetEnv : Values model target) (region : Region source) :
      denoteRegion model targetEnv (region.renameWires renameWires) ↔
        denoteRegion model (Values.rename renameWires targetEnv) region := by
    cases region with
    | mk locals items =>
        simp only [Region.renameWires, denoteRegion_mk]
        constructor
        · rintro ⟨localEnv, renamedDenotes⟩
          refine ⟨localEnv, ?_⟩
          have := (denoteItemSeq_renameWires model
            (renameWires.appendRight locals)
            (targetEnv.append localEnv) items).mp renamedDenotes
          rwa [renameAppendValues] at this
        · rintro ⟨localEnv, sourceDenotes⟩
          refine ⟨localEnv, ?_⟩
          apply (denoteItemSeq_renameWires model
            (renameWires.appendRight locals)
            (targetEnv.append localEnv) items).mpr
          rwa [renameAppendValues]

  theorem denoteItem_renameWires
      (model : Model) (renameWires : WireRenaming source target)
      (targetEnv : Values model target) (item : Item source) :
      denoteItem model targetEnv (item.renameWires renameWires) ↔
        denoteItem model (Values.rename renameWires targetEnv) item := by
    cases item with
    | atom head ports =>
        simp only [Item.renameWires, denoteItem_atom, Values.lookup_rename]
        have argumentsEq := evaluateVars_map_eq ports renameWires
          (Values.rename renameWires targetEnv) targetEnv
          (fun _ => Values.lookup_rename renameWires targetEnv _)
        rw [argumentsEq]
    | identity signature arity ports =>
        simp only [Item.renameWires, denoteItem_identity,
          Values.lookup_rename]
    | term output freeArity ports term =>
        simp only [Item.renameWires, denoteItem_term,
          Values.lookup_rename]
    | cut body =>
        simp only [Item.renameWires, denoteItem_cut]
        exact not_congr (denoteRegion_renameWires model
          renameWires targetEnv body)

  theorem denoteItemSeq_renameWires
      (model : Model) (renameWires : WireRenaming source target)
      (targetEnv : Values model target) (items : ItemSeq source) :
      denoteItemSeq model targetEnv (items.renameWires renameWires) ↔
        denoteItemSeq model (Values.rename renameWires targetEnv) items := by
    cases items with
    | nil => constructor <;> intro <;> trivial
    | cons head tail =>
        simp only [ItemSeq.renameWires, denoteItemSeq_cons]
        rw [denoteItem_renameWires, denoteItemSeq_renameWires]
end

private def localLeftRenaming (left right : List Sig) :
    WireRenaming left (left ++ right) :=
  ⟨fun wire => wire.appendLeft right⟩

private def localRightRenaming (left right : List Sig) :
    WireRenaming right (left ++ right) :=
  ⟨fun wire => Var.appendRight left wire⟩

private theorem renameLocalLeft_append
    (left : Values model leftContext) (right : Values model rightContext) :
    Values.rename (localLeftRenaming leftContext rightContext)
      (left.append right) = left := by
  apply Values.ext
  intro signature wire
  simp [localLeftRenaming]

private theorem renameLocalRight_append
    (left : Values model leftContext) (right : Values model rightContext) :
    Values.rename (localRightRenaming leftContext rightContext)
      (left.append right) = right := by
  apply Values.ext
  intro signature wire
  simp [localRightRenaming]

private theorem adjoinHostValues
    (outerEnv : Values model outer)
    (combined : Values model (hostLocals ++ addedLocals)) :
    Values.rename (Region.adjoinHostWire outer hostLocals addedLocals)
        (outerEnv.append combined) =
      outerEnv.append
        (Values.rename (localLeftRenaming hostLocals addedLocals) combined) := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (Values.rename (Region.adjoinHostWire outer hostLocals addedLocals)
        (outerEnv.append combined)).lookup wire =
      (outerEnv.append
        (Values.rename (localLeftRenaming hostLocals addedLocals) combined)).lookup wire)
  · intro signature inherited
    simp [Region.adjoinHostWire, Region.conjoinLeftWire]
  · intro signature localWire
    simp [Region.adjoinHostWire, Region.conjoinLeftWire,
      localLeftRenaming]

private theorem adjoinMaterialValues
    (outerEnv : Values model outer)
    (combined : Values model (hostLocals ++ addedLocals)) :
    Values.rename (Region.adjoinMaterialWire outer hostLocals addedLocals)
        (outerEnv.append combined) =
      (outerEnv.append
        (Values.rename (localLeftRenaming hostLocals addedLocals) combined)).append
        (Values.rename (localRightRenaming hostLocals addedLocals) combined) := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (Values.rename (Region.adjoinMaterialWire outer hostLocals addedLocals)
        (outerEnv.append combined)).lookup wire =
      ((outerEnv.append
        (Values.rename (localLeftRenaming hostLocals addedLocals) combined)).append
        (Values.rename (localRightRenaming hostLocals addedLocals) combined)).lookup wire)
  · intro signature prior
    apply Var.appendCases
      (motive := fun prior =>
        (Values.rename (Region.adjoinMaterialWire outer hostLocals addedLocals)
          (outerEnv.append combined)).lookup (prior.appendLeft addedLocals) =
        ((outerEnv.append
          (Values.rename (localLeftRenaming hostLocals addedLocals) combined)).append
          (Values.rename (localRightRenaming hostLocals addedLocals) combined)).lookup
            (prior.appendLeft addedLocals))
    · intro signature inherited
      simp [Region.adjoinMaterialWire]
    · intro signature localWire
      simp [Region.adjoinMaterialWire, localLeftRenaming]
  · intro signature addedWire
    simp [Region.adjoinMaterialWire, localRightRenaming]

private theorem conjoinRightValues
    (outerEnv : Values model outer)
    (combined : Values model (leftLocals ++ rightLocals)) :
    Values.rename (Region.conjoinRightWire outer leftLocals rightLocals)
        (outerEnv.append combined) =
      outerEnv.append
        (Values.rename (localRightRenaming leftLocals rightLocals)
          combined) := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (Values.rename
        (Region.conjoinRightWire outer leftLocals rightLocals)
        (outerEnv.append combined)).lookup wire =
      (outerEnv.append
        (Values.rename (localRightRenaming leftLocals rightLocals)
          combined)).lookup wire)
  · intro signature inherited
    simp [Region.conjoinRightWire]
  · intro signature localWire
    simp [Region.conjoinRightWire, localRightRenaming]

/-- Conjunction has exactly the semantics of both recursively scoped
operands. The combined region owns the operands' local wires disjointly. -/
theorem Region.denote_conjoin
    (model : Model) (outerEnv : Values model outer)
    (left right : Region outer) :
    denoteRegion model outerEnv (left.conjoin right) ↔
      denoteRegion model outerEnv left ∧
        denoteRegion model outerEnv right := by
  cases left with
  | mk leftLocals leftItems =>
      cases right with
      | mk rightLocals rightItems =>
          simp only [Region.conjoin, denoteRegion_mk,
            denoteItemSeq_append]
          constructor
          · rintro ⟨combined, leftDenotes, rightDenotes⟩
            let leftEnv := Values.rename
              (localLeftRenaming leftLocals rightLocals) combined
            let rightEnv := Values.rename
              (localRightRenaming leftLocals rightLocals) combined
            constructor
            · refine ⟨leftEnv, ?_⟩
              have := (denoteItemSeq_renameWires model
                (Region.conjoinLeftWire outer leftLocals rightLocals)
                (outerEnv.append combined) leftItems).mp leftDenotes
              have valuesEq := adjoinHostValues
                (outerEnv := outerEnv) (hostLocals := leftLocals)
                (addedLocals := rightLocals) combined
              change Values.rename
                  (Region.conjoinLeftWire outer leftLocals rightLocals)
                  (outerEnv.append combined) =
                outerEnv.append (Values.rename
                  (localLeftRenaming leftLocals rightLocals) combined)
                at valuesEq
              rw [valuesEq] at this
              exact this
            · refine ⟨rightEnv, ?_⟩
              have := (denoteItemSeq_renameWires model
                (Region.conjoinRightWire outer leftLocals rightLocals)
                (outerEnv.append combined) rightItems).mp rightDenotes
              simpa only [rightEnv, conjoinRightValues] using this
          · rintro ⟨⟨leftEnv, leftDenotes⟩,
                ⟨rightEnv, rightDenotes⟩⟩
            let combined := leftEnv.append rightEnv
            refine ⟨combined, ?_, ?_⟩
            · apply (denoteItemSeq_renameWires model
                (Region.conjoinLeftWire outer leftLocals rightLocals)
                (outerEnv.append combined) leftItems).mpr
              have valuesEq := adjoinHostValues
                (outerEnv := outerEnv) (hostLocals := leftLocals)
                (addedLocals := rightLocals) combined
              change Values.rename
                  (Region.conjoinLeftWire outer leftLocals rightLocals)
                  (outerEnv.append combined) =
                outerEnv.append (Values.rename
                  (localLeftRenaming leftLocals rightLocals) combined)
                at valuesEq
              rw [valuesEq]
              change denoteItemSeq model
                (outerEnv.append (Values.rename
                  (localLeftRenaming leftLocals rightLocals) combined))
                leftItems
              rw [show Values.rename
                  (localLeftRenaming leftLocals rightLocals) combined =
                    leftEnv by
                exact renameLocalLeft_append leftEnv rightEnv]
              exact leftDenotes
            · apply (denoteItemSeq_renameWires model
                (Region.conjoinRightWire outer leftLocals rightLocals)
                (outerEnv.append combined) rightItems).mpr
              rw [conjoinRightValues]
              change denoteItemSeq model
                (outerEnv.append (Values.rename
                  (localRightRenaming leftLocals rightLocals) combined))
                rightItems
              rw [show Values.rename
                  (localRightRenaming leftLocals rightLocals) combined =
                    rightEnv by
                exact renameLocalRight_append leftEnv rightEnv]
              exact rightDenotes

theorem Region.denote_adjoinAt
    (model : Model) (outerEnv : Values model outer)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) :
    denoteRegion model outerEnv
        (Region.adjoinAt hostLocals hostItems material) ↔
      ∃ hostEnv : Values model hostLocals,
        denoteItemSeq model (outerEnv.append hostEnv) hostItems ∧
          denoteRegion model (outerEnv.append hostEnv) material := by
  cases material with
  | mk addedLocals addedItems =>
      simp only [Region.adjoinAt, denoteRegion_mk, denoteItemSeq_append]
      constructor
      · rintro ⟨combined, hostDenotes, materialDenotes⟩
        let hostEnv := Values.rename
          (localLeftRenaming hostLocals addedLocals) combined
        let addedEnv := Values.rename
          (localRightRenaming hostLocals addedLocals) combined
        refine ⟨hostEnv, ?_, ⟨addedEnv, ?_⟩⟩
        · have := (denoteItemSeq_renameWires model
            (Region.adjoinHostWire outer hostLocals addedLocals)
            (outerEnv.append combined) hostItems).mp hostDenotes
          simpa only [hostEnv, adjoinHostValues] using this
        · have := (denoteItemSeq_renameWires model
            (Region.adjoinMaterialWire outer hostLocals addedLocals)
            (outerEnv.append combined) addedItems).mp materialDenotes
          simpa only [hostEnv, addedEnv, adjoinMaterialValues] using this
      · rintro ⟨hostEnv, hostDenotes, addedEnv, materialDenotes⟩
        let combined := hostEnv.append addedEnv
        refine ⟨combined, ?_, ?_⟩
        · apply (denoteItemSeq_renameWires model
            (Region.adjoinHostWire outer hostLocals addedLocals)
            (outerEnv.append combined) hostItems).mpr
          rw [adjoinHostValues]
          rw [show Values.rename
            (localLeftRenaming hostLocals addedLocals) combined = hostEnv by
              exact renameLocalLeft_append hostEnv addedEnv]
          exact hostDenotes
        · apply (denoteItemSeq_renameWires model
            (Region.adjoinMaterialWire outer hostLocals addedLocals)
            (outerEnv.append combined) addedItems).mpr
          rw [adjoinMaterialValues]
          rw [show Values.rename
            (localLeftRenaming hostLocals addedLocals) combined = hostEnv by
              exact renameLocalLeft_append hostEnv addedEnv]
          rw [show Values.rename
            (localRightRenaming hostLocals addedLocals) combined = addedEnv by
              exact renameLocalRight_append hostEnv addedEnv]
          exact materialDenotes

theorem Region.denote_spliceAt
    (model : Model) (outerEnv : Values model outer)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region materialWires)
    (wireMap : WireRenaming materialWires (outer ++ hostLocals)) :
    denoteRegion model outerEnv
        (Region.spliceAt hostLocals hostItems material wireMap) ↔
      ∃ hostEnv : Values model hostLocals,
        denoteItemSeq model (outerEnv.append hostEnv) hostItems ∧
          denoteRegion model
            (Values.rename wireMap (outerEnv.append hostEnv)) material := by
  rw [Region.spliceAt, Region.denote_adjoinAt]
  constructor
  · rintro ⟨hostEnv, hostDenotes, materialDenotes⟩
    exact ⟨hostEnv, hostDenotes,
      (denoteRegion_renameWires model wireMap
        (outerEnv.append hostEnv) material).mp materialDenotes⟩
  · rintro ⟨hostEnv, hostDenotes, materialDenotes⟩
    exact ⟨hostEnv, hostDenotes,
      (denoteRegion_renameWires model wireMap
        (outerEnv.append hostEnv) material).mpr materialDenotes⟩

end VisualProof.Diagram
