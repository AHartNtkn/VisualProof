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

end VisualProof.Diagram
