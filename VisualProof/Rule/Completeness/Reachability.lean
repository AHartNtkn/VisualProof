import VisualProof.Rule.Step

namespace Relation

/-- Reflexive-transitive closure, kept minimal for optional completeness
phases around a mandatory primitive core. -/
inductive ReflTransGen (relation : α → α → Prop) : α → α → Prop
  | refl : ReflTransGen relation value value
  | tail : ReflTransGen relation first middle →
      relation middle last → ReflTransGen relation first last

namespace ReflTransGen

theorem trans
    (first : ReflTransGen relation source middle)
    (second : ReflTransGen relation middle target) :
    ReflTransGen relation source target := by
  induction second with
  | refl => exact first
  | tail _ step induction => exact .tail induction step

/-- An optional prefix followed by a mandatory core remains mandatory. -/
theorem transGen
    (optionalPrefix : ReflTransGen relation source middle)
    (core : TransGen relation middle target) :
    TransGen relation source target := by
  induction optionalPrefix with
  | refl => exact core
  | tail _ step induction =>
      exact induction ((TransGen.single step).trans core)

end ReflTransGen

namespace TransGen

/-- A mandatory core followed by an optional suffix remains mandatory. -/
theorem reflTransGen
    (core : TransGen relation source middle)
    (suffix : ReflTransGen relation middle target) :
    TransGen relation source target := by
  induction suffix with
  | refl => exact core
  | tail _ step induction => exact induction.tail step

end TransGen

end Relation

namespace VisualProof.Rule.Completeness

open Diagram
open Theory

/-- Transport every endpoint of a nonempty primitive derivation through open
diagram isomorphism. -/
theorem transGen_iso
    {boundary : List Sig}
    {source source' target target' : OpenDiagram boundary}
    (sourceIso : OpenDiagramIso source source')
    (steps : Relation.TransGen Step source target)
    (targetIso : OpenDiagramIso target target') :
    Relation.TransGen Step source' target' := by
  induction steps generalizing source' target' with
  | single step =>
      exact .single (Step.iso sourceIso step targetIso)
  | tail steps step induction =>
      exact (induction sourceIso (OpenDiagramIso.refl _)).tail
        (Step.iso (OpenDiagramIso.refl _) step targetIso)

/-- The canonical occurrence whose host is exactly the filled diagram. -/
noncomputable def exactOccurrence
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (pattern : Region holeWires)
    (sourceCanonical : (context.fill pattern).Canonical)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill pattern)) :
    Occurrence pattern
      (interface.withBody (context.fill pattern) sourceCanonical
        sourceExternalTwoEnded) where
  interface := interface
  context := context
  sourceCanonical := sourceCanonical
  sourceExternalTwoEnded := sourceExternalTwoEnded
  host_iso := OpenDiagramIso.refl _

/-- Bidirectional optional reachability between the exact endpoints of one
actual occurrence. Deep equality phases use this instead of forgetting that
every primitive below the binder home is symmetric. -/
def Equates
    {boundary holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (after : Region holeWires)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)) : Prop :=
  let target := occurrence.interface.withBody
    (occurrence.context.fill after) targetCanonical targetExternalTwoEnded
  Relation.ReflTransGen Step source target ∧
    Relation.ReflTransGen Step target source

/-- An optional internal derivation from one actual occurrence to the exact
filled target supplied by the caller. The polarity index records the
occurrence's current polarity rather than recomputing a separate direction. -/
def Derives
    {boundary holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    (polarity : Polarity)
    (occurrence : Occurrence before source)
    (after : Region holeWires)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)) : Prop :=
  occurrence.context.polarity = polarity ∧
    Relation.ReflTransGen Step source
      (occurrence.interface.withBody (occurrence.context.fill after)
        targetCanonical targetExternalTwoEnded)

/-- Consecutive phases at the same concrete occurrence compose without a
region-level derivability relation. -/
theorem Derives.trans
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {polarity : Polarity}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (first : Derives polarity occurrence middle middleCanonical
      middleExternalTwoEnded)
    (second : Derives polarity
      (exactOccurrence occurrence.interface occurrence.context middle
        middleCanonical middleExternalTwoEnded)
      after targetCanonical targetExternalTwoEnded) :
    Derives polarity occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨first.1, first.2.trans second.2⟩

/-- Inject one contextual primitive at the occurrence's recorded polarity. -/
theorem transGen_contextual
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    {polarity : Polarity}
    (localRule : LocalRule)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after))
    (polarityEq : occurrence.context.polarity = polarity)
    (localStep : atPolarity polarity localRule before after)
    (inject : ∀ {stepBoundary : List Sig}
      {source target : OpenDiagram stepBoundary},
      Contextual localRule source target → Step source target) :
    Relation.TransGen Step source
      (occurrence.interface.withBody (occurrence.context.fill after)
        targetCanonical targetExternalTwoEnded) := by
  have atOccurrence :
      atPolarity occurrence.context.polarity localRule before after := by
    simpa [polarityEq] using localStep
  exact .single (inject ⟨_, before, after, occurrence,
    targetCanonical, targetExternalTwoEnded, OpenDiagramIso.refl _,
    atOccurrence⟩)

/-- Introduce one temporary support pin, retaining both primitive directions. -/
theorem pinStep
    {boundary holeWires locals : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (Vacuity.Pin.plain locals items) source)
    (signature : Sig) (wire : Var (holeWires ++ locals) signature) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (Vacuity.Pin.present locals items signature wire)).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Vacuity.Pin.present locals items signature wire)),
        Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Vacuity.Pin.present locals items signature wire))
              targetCanonical targetExternalTwoEnded) ∧
          Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Vacuity.Pin.present locals items signature wire))
              targetCanonical targetExternalTwoEnded)
            source := by
  have validity := Vacuity.Pin.introduceValidity occurrence signature wire
  let step : Vacuity source
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Vacuity.Pin.present locals items signature wire))
        validity.1 validity.2) := ⟨holeWires, Vacuity.Pin.plain locals items,
    Vacuity.Pin.present locals items signature wire, occurrence,
    validity.1, validity.2, OpenDiagramIso.refl _,
    atPolarity_symmetric_of occurrence.context.polarity
      (.mk (.pin locals items signature wire))⟩
  exact ⟨validity.1, validity.2,
    Step.vacuity step, Step.vacuity step.symm⟩

end VisualProof.Rule.Completeness
