import VisualProof.Rule.Completeness.Erasure.Exposure
import VisualProof.Rule.Completeness.Comprehension.Sites
import VisualProof.Rule.Iteration

namespace VisualProof.Rule.Completeness.Erasure.Duplication

open Diagram
open Theory

/-- Iteration with no freshened wires redirects every selected wire through
the descendant identity context. -/
def emptyFreshening
    (inherited : WireRenaming sourceWires targetWires) :
    Iteration.WireFreshening sourceWires targetWires [] inherited where
  sourceOfFresh := ⟨fun wire => nomatch wire⟩
  sourceOfFresh_injective := by
    intro signature left
    exact nomatch left
  wire := ⟨fun wire => (inherited wire).appendLeft []⟩
  wire_fresh := by
    intro signature fresh
    exact nomatch fresh
  wire_inherited := by
    intro signature source _
    rfl

noncomputable def exposedSelectedSourceIso
    (description : Rule.UncappedErasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl outer)
      (Exposure.exposedRegion description materialCanonical)
      (Region.adjoinAt description.hostLocals .nil
        ((Comprehension.Instantiation.instantiate
            (Exposure.supportPattern description.material
              materialCanonical)
            (Exposure.applicationPorts description)).conjoin
          (Comprehension.retainedItemsPresentation
            description.hostItems))) := by
  let specialized := Comprehension.Instantiation.instantiate
    (Exposure.supportPattern description.material materialCanonical)
    (Exposure.applicationPorts description)
  let retained := Comprehension.retainedItemsPresentation
    description.hostItems
  let retainedIso := Comprehension.retainedItemsPresentationIso
    description.hostItems
  let retainedPresented := RegionIso.adjoinAt description.hostLocals .nil
    (RegionIso.conjoinCongr (RegionIso.refl specialized) retainedIso)
  let swapped := RegionIso.adjoinAt description.hostLocals .nil
    (RegionIso.conjoinComm specialized
      (Region.ofItems description.hostItems))
  let hosted := adjoinAt_hostedMaterial description.hostLocals
    description.hostItems specialized
  let closed := RegionIso.ofEq hosted.symm
  have chain := (retainedPresented.trans swapped).trans closed
  have ambientEq :
      ((WireEquiv.refl outer).trans (WireEquiv.refl outer)).trans
          (WireEquiv.refl outer) =
        WireEquiv.refl outer := by
    apply WireEquiv.ext
    intro signature wire
    rfl
  let chain' := chain.castAmbient ambientEq
  simpa only [Exposure.exposedRegion, specialized, retained] using chain'.symm

noncomputable def copyBlockEmptyIso
    (selected : Region sourceWires)
    (inherited : WireRenaming sourceWires targetWires) :
    RegionIso (WireEquiv.refl targetWires)
      (Iteration.copyBlock selected (emptyFreshening inherited))
      (selected.renameWires inherited) := by
  let appended : WireRenaming targetWires (targetWires ++ []) :=
    (WireEquiv.appendNil targetWires).symm.toRenaming
  have wireEq : (emptyFreshening inherited).wire =
      WireRenaming.comp appended inherited := by
    apply WireRenaming.ext
    intro signature wire
    exact (WireEquiv.appendNil_symm_apply targetWires
      (inherited wire)).symm
  have renamedEq :
      selected.renameWires (emptyFreshening inherited).wire =
        (selected.renameWires inherited).renameWires appended := by
    rw [wireEq, Region.renameWires_comp]
  have presented :=
    (RegionIso.adjoinAtNilRenamed
      (selected.renameWires inherited)).symm
  simpa only [Iteration.copyBlock, Iteration.freshPins,
    Iteration.freshenedSelected, ItemSeq.rootedTwoPins, ItemSeq.pinWires,
    ItemSeq.nil_append, renamedEq, appended] using presented

noncomputable def exposedNestedOccurrence
    {boundary outer : List Sig}
    (description : Rule.UncappedErasure.Description outer)
    (materialCanonical : description.material.Canonical)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Exposure.exposedRegion description materialCanonical) source) :
    NestedOccurrence source := by
  let selected := Comprehension.Instantiation.instantiate
    (Exposure.supportPattern description.material materialCanonical)
    (Exposure.applicationPorts description)
  let remainder := Comprehension.retainedItemsPresentation
    description.hostItems
  let localSource := Region.adjoinAt description.hostLocals .nil
    (selected.conjoin remainder)
  let localIso := exposedSelectedSourceIso description materialCanonical
  let filledIso := occurrence.context.fillIso localIso
  have nestedCanonical :
      (occurrence.context.fill localSource).Canonical := by
    exact filledIso.canonical_iff.mp occurrence.sourceCanonical
  have nestedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill localSource) := by
    intro signature wire
    rw [← filledIso.incidencePaths_length_eq wire]
    exact occurrence.sourceExternalTwoEnded wire
  let nestedOpenIso : OpenDiagramIso
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Exposure.exposedRegion description materialCanonical))
        occurrence.sourceCanonical occurrence.sourceExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill localSource)
        nestedCanonical nestedExternalTwoEnded) :=
    OpenDiagram.withBody_iso occurrence.sourceCanonical nestedCanonical
      occurrence.sourceExternalTwoEnded nestedExternalTwoEnded filledIso
  exact {
    ancestorWires := outer
    anchorLocals := description.hostLocals
    descendantWires := outer ++ description.hostLocals
    selected := selected
    before := remainder
    interface := occurrence.interface
    outer := occurrence.context
    descendant := .hole
    sourceCanonical := by
      simpa only [nestedBody, DiagramContext.fill, localSource] using
        nestedCanonical
    sourceExternalTwoEnded := by
      intro signature wire
      simpa only [nestedBody, DiagramContext.fill, localSource] using
        nestedExternalTwoEnded wire
    source_iso := by
      exact occurrence.host_iso.trans nestedOpenIso
  }

/-- A selected block duplicates with no fresh wires to any pin-free endpoint
isomorphic to Iteration's raw copy. -/
theorem copyStep
    {boundary : List Sig} {source : OpenDiagram boundary}
    (occurrence : NestedOccurrence source)
    (targetBody : Region occurrence.interface.external)
    (targetPresentation : RegionIso
      (WireEquiv.refl occurrence.interface.external)
      (occurrence.targetBody
        ((occurrence.selected.renameWires
            occurrence.descendant.outerWire).conjoin occurrence.before))
      targetBody)
    (targetCanonical : targetBody.Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      targetBody) :
    Rule.Iteration source
      (occurrence.interface.withBody
        targetBody targetCanonical targetExternalTwoEnded) := by
  let copiedBlockPresentation := copyBlockEmptyIso occurrence.selected
    occurrence.descendant.outerWire
  let copiedPresentation : RegionIso
      (WireEquiv.refl occurrence.descendantWires)
      (Iteration.copied occurrence.selected occurrence.before
        (emptyFreshening occurrence.descendant.outerWire))
      ((occurrence.selected.renameWires
          occurrence.descendant.outerWire).conjoin occurrence.before) :=
    RegionIso.conjoinCongr copiedBlockPresentation
      (RegionIso.refl occurrence.before)
  let descendantPresentation := occurrence.descendant.fillIso
    copiedPresentation
  let selectedPresentation := RegionIso.conjoinCongr
    (RegionIso.refl occurrence.selected) descendantPresentation
  let anchoredPresentation := RegionIso.adjoinAt occurrence.anchorLocals .nil
    selectedPresentation
  let rawPresentation := occurrence.outer.fillIso anchoredPresentation
  let composedPresentation := rawPresentation.trans targetPresentation
  have ambientEq :
      (WireEquiv.refl occurrence.interface.external).trans
          (WireEquiv.refl occurrence.interface.external) =
        WireEquiv.refl occurrence.interface.external := by
    apply WireEquiv.ext
    intro signature wire
    rfl
  let fullPresentation : RegionIso
      (WireEquiv.refl occurrence.interface.external)
      (occurrence.targetBody
        (Iteration.copied occurrence.selected occurrence.before
          (emptyFreshening occurrence.descendant.outerWire)))
      targetBody := by
    simpa only [NestedOccurrence.targetBody, nestedBody] using
      composedPresentation.castAmbient ambientEq
  have rawCanonical :
      (occurrence.targetBody
        (Iteration.copied occurrence.selected occurrence.before
          (emptyFreshening occurrence.descendant.outerWire))).Canonical :=
    fullPresentation.canonical_iff.mpr targetCanonical
  have rawExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.targetBody
        (Iteration.copied occurrence.selected occurrence.before
          (emptyFreshening occurrence.descendant.outerWire))) := by
    intro signature wire
    rw [fullPresentation.incidencePaths_length_eq wire]
    exact targetExternalTwoEnded wire
  let rawTarget := occurrence.replace
    (Iteration.copied occurrence.selected occurrence.before
      (emptyFreshening occurrence.descendant.outerWire))
    rawCanonical rawExternalTwoEnded
  let targetIso : OpenDiagramIso
      (occurrence.interface.withBody
        targetBody targetCanonical targetExternalTwoEnded)
      rawTarget :=
    (OpenDiagram.withBody_iso rawCanonical targetCanonical
      rawExternalTwoEnded targetExternalTwoEnded fullPresentation).symm
  exact ⟨occurrence,
    Iteration.copied occurrence.selected occurrence.before
      (emptyFreshening occurrence.descendant.outerWire),
    rawCanonical, rawExternalTwoEnded, targetIso,
    Or.inl (.copy occurrence.before []
      (emptyFreshening occurrence.descendant.outerWire))⟩

/-- Specialize pin-free Iteration to an erasure exposure.  The result body is
chosen by the caller and is required only to present the raw copied body up to
isomorphism. -/
theorem exposedCopyStep
    {boundary outer : List Sig}
    (description : Rule.UncappedErasure.Description outer)
    (materialCanonical : description.material.Canonical)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Exposure.exposedRegion description materialCanonical) source)
    (targetBody : Region occurrence.interface.external)
    (targetPresentation : RegionIso
      (WireEquiv.refl occurrence.interface.external)
      ((exposedNestedOccurrence description materialCanonical occurrence).targetBody
        (((exposedNestedOccurrence description materialCanonical occurrence).selected.renameWires
            (exposedNestedOccurrence description materialCanonical occurrence).descendant.outerWire).conjoin
          (exposedNestedOccurrence description materialCanonical occurrence).before))
      targetBody)
    (targetCanonical : targetBody.Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire targetBody) :
    Rule.Iteration source
      (occurrence.interface.withBody targetBody targetCanonical
        targetExternalTwoEnded) := by
  exact copyStep
    (exposedNestedOccurrence description materialCanonical occurrence) targetBody
    targetPresentation targetCanonical targetExternalTwoEnded

end VisualProof.Rule.Completeness.Erasure.Duplication
