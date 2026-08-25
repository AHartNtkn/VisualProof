import VisualProof.Rule.Completeness.Comprehension.Leaf.Complete

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

/-- The exact production claim used as the structural recursion motive. -/
def SupportDerives {materialWires : List Sig}
    (material : Region materialWires) : Prop :=
  ∀ (materialCanonical : material.Canonical)
    {structuralOuter structuralBefore structuralAfter : List Sig}
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel materialWires :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern material materialCanonical)
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter materialWires)
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter materialWires)
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
        items)),
    request.Result

/-- A region with no outer or local wires delegates to its item sequence. -/
theorem supportItemsDerives
    {materialItems : ItemSeq []}
    (materialItemsIH : SupportDerives (Region.ofItems materialItems)) :
    SupportDerives (Region.mk [] materialItems : Region []) := by
  intro materialCanonical structuralOuter structuralBefore structuralAfter
    items result evidence structuralRequest
  have materialEq : Region.ofItems materialItems =
      (Region.mk [] materialItems : Region []) := by
    simp only [Region.ofItems]
    congr 1
    let appendNil : WireRenaming [] ([] ++ []) :=
      ⟨fun wire => wire.appendLeft []⟩
    change materialItems.renameWires appendNil = materialItems
    have renameEq : appendNil = WireRenaming.id := by
      apply WireRenaming.ext
      intro signature wire
      cases wire
    rw [renameEq]
    exact ItemSeq.renameWires_id materialItems
  have materialItemsCanonical :
      (Region.ofItems materialItems).Canonical := by
    rw [materialEq]
    exact materialCanonical
  have patternEq :
      Erasure.Exposure.supportPattern
          (Region.mk [] materialItems : Region []) materialCanonical =
        Erasure.Exposure.supportPattern
          (Region.ofItems materialItems) materialItemsCanonical := by
    apply EqualityNormalization.OpenDiagram.eq_of_data
    · rfl
    · rfl
    · change (HEq
        (Erasure.Exposure.supportBody (Region.mk [] materialItems : Region []))
        (Erasure.Exposure.supportBody (Region.ofItems materialItems)))
      have sourceBodyEq :
          Erasure.Exposure.supportBody
              (Region.mk [] materialItems : Region []) =
            (Region.mk [] materialItems : Region []) :=
        EqualityNormalization.supportBody_eq_of_supportPins_nil
          (Region.mk [] materialItems : Region []) rfl
      have targetBodyEq :
          Erasure.Exposure.supportBody (Region.ofItems materialItems) =
            Region.ofItems materialItems :=
        EqualityNormalization.supportBody_eq_of_supportPins_nil
          (Region.ofItems materialItems) rfl
      have bodyEq := sourceBodyEq.trans
        (materialEq.symm.trans targetBodyEq.symm)
      exact heq_of_eq bodyEq
  rw [patternEq] at evidence
  exact materialItemsIH materialItemsCanonical evidence structuralRequest

theorem polaritySource_property
    (polarity : Polarity) (property : α → Prop) (before after : α)
    (beforeProperty : property before) (afterProperty : property after) :
    property (polaritySource polarity before after) := by
  cases polarity
  · exact beforeProperty
  · exact afterProperty

end Structural

end VisualProof.Rule.Completeness.Comprehension
