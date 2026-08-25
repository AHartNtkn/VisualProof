import VisualProof.Rule.Completeness.Comprehension.Structural.Arity

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory

namespace Structural

/-- The zero-local presentation produced by `Region.ofItems` transports to
the corresponding region constructor without changing the derivability
claim. -/
theorem supportZeroLocalDerives
    {outer : List Sig} (materialItems : ItemSeq (outer ++ []))
    (materialItemsIH : SupportDerives (Region.ofItems materialItems)) :
    SupportDerives (Region.mk [] materialItems : Region outer) := by
  let contextEq : outer ++ [] = outer := List.append_nil outer
  have castRegionEq : ∀ {source target : List Sig}
      (equality : source = target) (region : Region source),
      equality ▸ region =
        region.renameWires (WireEquiv.ofEq equality).toRenaming := by
    intro source target equality region
    subst target
    exact (Region.renameWires_id region).symm
  have contextEquivEq :
      WireEquiv.ofEq contextEq = WireEquiv.appendNil outer := by
    apply WireEquiv.ext
    intro signature wire
    apply Var.eq_of_index_eq
    apply Fin.ext
    rw [WireEquiv.ofEq_index_val]
    apply Var.appendCases (left := outer) (right := [])
      (motive := fun wire =>
        wire.index.val = (WireEquiv.appendNil outer wire).index.val)
      (wire := wire)
    · intro inheritedSignature inherited
      simp [WireEquiv.appendNil_apply]
    · intro emptySignature emptyWire
      exact nomatch emptyWire
  have collapsedOfItems :
      (Region.ofItems materialItems).renameWires
          (WireEquiv.appendNil outer).toRenaming =
        (Region.mk [] materialItems : Region outer) := by
    rw [Region.ofItems_renameWires]
    unfold Region.ofItems
    change Region.mk []
        ((materialItems.renameWires
          (WireEquiv.appendNil outer).toRenaming).renameWires
            (⟨fun wire => wire.appendLeft []⟩ :
              WireRenaming outer (outer ++ []))) =
          Region.mk [] materialItems
    rw [ItemSeq.renameWires_comp]
    have renameEq : WireRenaming.comp
        (⟨fun wire => wire.appendLeft []⟩ :
          WireRenaming outer (outer ++ []))
        (WireEquiv.appendNil outer).toRenaming = WireRenaming.id := by
      apply WireRenaming.ext
      intro signature wire
      change
        ((WireEquiv.appendNil outer).toRenaming wire).appendLeft [] = wire
      rw [← WireEquiv.appendNil_symm_apply]
      exact (WireEquiv.appendNil outer).left_inv wire
    rw [renameEq, ItemSeq.renameWires_id]
  have materialEq : contextEq ▸ Region.ofItems materialItems =
      (Region.mk [] materialItems : Region outer) := by
    rw [castRegionEq, contextEquivEq]
    exact collapsedOfItems
  have castDerives : ∀ {source target : List Sig}
      (equality : source = target) (material : Region source),
      SupportDerives material → SupportDerives (equality ▸ material) := by
    intro source target equality material derives
    subst target
    exact derives
  rw [← materialEq]
  exact castDerives contextEq _ materialItemsIH

/-- A region is derivable from its recursively derived item sequence at any
inherited and local wire context. -/
theorem supportRegionDerives
    {outer : List Sig} (locals : List Sig)
    (materialItems : ItemSeq (outer ++ locals))
    (materialItemsIH : SupportDerives (Region.ofItems materialItems)) :
    SupportDerives (Region.mk locals materialItems : Region outer) := by
  cases locals with
  | nil => exact supportZeroLocalDerives materialItems materialItemsIH
  | cons firstLocal remainingLocals =>
      let reassociateEq :
          outer ++ firstLocal :: remainingLocals =
            (outer ++ [firstLocal]) ++ remainingLocals := by
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      let exposedItems := arityExposedItems outer firstLocal remainingLocals
        materialItems
      have castRegionEq : ∀ {source target : List Sig}
          (equality : source = target) (region : Region source),
          equality ▸ region =
            region.renameWires (WireEquiv.ofEq equality).toRenaming := by
        intro source target equality region
        subst target
        exact (Region.renameWires_id region).symm
      have exposedMaterialEq :
          reassociateEq ▸ Region.ofItems materialItems =
            Region.ofItems exposedItems := by
        rw [castRegionEq, Region.ofItems_renameWires]
        unfold exposedItems arityExposedItems
        congr 2
      have castDerives : ∀ {source target : List Sig}
          (equality : source = target) (material : Region source),
          SupportDerives material →
            SupportDerives (equality ▸ material) := by
        intro source target equality material derives
        subst target
        exact derives
      have exposedItemsIH : SupportDerives (Region.ofItems exposedItems) := by
        rw [← exposedMaterialEq]
        exact castDerives reassociateEq _ materialItemsIH
      have childDerives : SupportDerives
          (arityExposedMaterial outer firstLocal remainingLocals
            materialItems) := by
        exact supportRegionDerives remainingLocals exposedItems exposedItemsIH
      intro materialCanonical structuralOuter structuralBefore
        structuralAfter items result evidence request
      exact supportArityDerives materialItems materialCanonical childDerives
        evidence request
termination_by locals.length

end Structural

end VisualProof.Rule.Completeness.Comprehension
