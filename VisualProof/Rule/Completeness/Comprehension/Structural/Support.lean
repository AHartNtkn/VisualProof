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

theorem filledValidityOfScope
    {boundary wires : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external wires)
    (before after : Region wires)
    (beforeCanonical : (context.fill before).Canonical)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before))
    (scope : ScopePreservation before after) :
    (context.fill after).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill after) := by
  have afterCanonical : after.Canonical := scope.canonical
    (context.holeCanonical before beforeCanonical)
  have replacement := context.replaceCanonical before after beforeCanonical
    afterCanonical scope.incidenceNonempty
  let beforeEndpoint := interface.withBody (context.fill before)
    beforeCanonical beforeExternalTwoEnded
  exact ⟨replacement.1,
    beforeEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2⟩

theorem telescopeTrans
    {boundary wires : List Sig}
    {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external wires}
    {first middle last : Region wires}
    {firstCanonical : (context.fill first).Canonical}
    {firstExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill first)}
    {middleCanonical : (context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill middle)}
    {lastCanonical : (context.fill last).Canonical}
    {lastExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill last)}
    (head : Telescope polarity interface context first middle
      firstCanonical firstExternalTwoEnded middleCanonical
      middleExternalTwoEnded)
    (tail : Telescope polarity interface context middle last
      middleCanonical middleExternalTwoEnded lastCanonical
      lastExternalTwoEnded) :
    Telescope polarity interface context first last firstCanonical
      firstExternalTwoEnded lastCanonical lastExternalTwoEnded := by
  cases polarity with
  | positive => exact ⟨head.1, head.2.trans tail.2⟩
  | negative => exact ⟨head.1, tail.2.trans head.2⟩

theorem polaritySource_property
    (polarity : Polarity) (property : α → Prop) (before after : α)
    (beforeProperty : property before) (afterProperty : property after) :
    property (polaritySource polarity before after) := by
  cases polarity
  · exact beforeProperty
  · exact afterProperty

theorem telescopeIso
    {boundary wires : List Sig} {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external wires}
    {before before' after after' : Region wires}
    {beforeCanonical : (context.fill before).Canonical}
    {beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before)}
    {beforeCanonical' : (context.fill before').Canonical}
    {beforeExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before')}
    {afterCanonical : (context.fill after).Canonical}
    {afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after)}
    {afterCanonical' : (context.fill after').Canonical}
    {afterExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after')}
    (beforeIso : RegionIso (WireEquiv.refl wires) before before')
    (afterIso : RegionIso (WireEquiv.refl wires) after after')
    (telescope : Telescope polarity interface context before after
      beforeCanonical beforeExternalTwoEnded afterCanonical
      afterExternalTwoEnded) :
    Telescope polarity interface context before' after'
      beforeCanonical' beforeExternalTwoEnded' afterCanonical'
      afterExternalTwoEnded' := by
  let beforeOpenIso := OpenDiagram.withBody_iso beforeCanonical
    beforeCanonical' beforeExternalTwoEnded beforeExternalTwoEnded'
    (DiagramContext.fillIso context beforeIso)
  let afterOpenIso := OpenDiagram.withBody_iso afterCanonical
    afterCanonical' afterExternalTwoEnded afterExternalTwoEnded'
    (DiagramContext.fillIso context afterIso)
  cases polarity with
  | positive =>
      exact ⟨telescope.1, EqualityNormalization.reflTransGen_iso
        beforeOpenIso telescope.2 afterOpenIso⟩
  | negative =>
      exact ⟨telescope.1, EqualityNormalization.reflTransGen_iso
        afterOpenIso telescope.2 beforeOpenIso⟩

theorem telescopeOfHosted
    {common outer hostLocals boundary : List Sig}
    {before after : Region common}
    (transformation : HostedStrict before after)
    (rename : WireRenaming common (outer ++ hostLocals))
    (hostItems : ItemSeq (outer ++ hostLocals))
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (beforeCanonical :
      (context.fill (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename))).Canonical)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename))))
    (afterCanonical :
      (context.fill (Region.adjoinAt hostLocals hostItems
        (after.renameWires rename))).Canonical)
    (afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (Region.adjoinAt hostLocals hostItems
        (after.renameWires rename))))
    (polarityEq : context.polarity = polarity) :
    Telescope polarity interface context
      (Region.adjoinAt hostLocals hostItems (before.renameWires rename))
      (Region.adjoinAt hostLocals hostItems (after.renameWires rename))
      beforeCanonical beforeExternalTwoEnded afterCanonical
      afterExternalTwoEnded := by
  let beforeHosted := Region.adjoinAt hostLocals hostItems
    (before.renameWires rename)
  let afterHosted := Region.adjoinAt hostLocals hostItems
    (after.renameWires rename)
  let occurrence := exactOccurrence interface context beforeHosted
    beforeCanonical beforeExternalTwoEnded
  have strict := transformation outer hostLocals rename hostItems occurrence
    afterCanonical afterExternalTwoEnded
  have equates := strict.toEquates
  cases polarity with
  | positive => exact ⟨polarityEq, equates.1⟩
  | negative => exact ⟨polarityEq, equates.2⟩

end Structural

end VisualProof.Rule.Completeness.Comprehension
