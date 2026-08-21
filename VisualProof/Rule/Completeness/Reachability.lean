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

/-- Refine an actual occurrence through one further exact recursive context.
The composed context is the only occurrence path; `fill_comp` identifies its
source with the caller's actual filled endpoint. -/
noncomputable def Occurrence.nest
    {boundary middle holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    {inner : DiagramContext middle holeWires}
    (occurrence : Occurrence (inner.fill before) source) :
    Occurrence before source where
  interface := occurrence.interface
  context := occurrence.context.comp inner
  sourceCanonical := by
    simpa only [DiagramContext.fill_comp] using occurrence.sourceCanonical
  sourceExternalTwoEnded := by
    intro signature wire
    simpa only [DiagramContext.fill_comp] using
      occurrence.sourceExternalTwoEnded wire
  host_iso := by
    simpa only [DiagramContext.fill_comp] using occurrence.host_iso

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

/-- Bidirectional nonempty reachability between exact occurrence endpoints.
This stronger internal form permits endpoint presentation transport while
the public equality phase remains optional when no selected site exists. -/
def StrictEquates
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
  Relation.TransGen Step source target ∧
    Relation.TransGen Step target source

theorem StrictEquates.toEquates
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)}
    (strict : StrictEquates occurrence after targetCanonical
      targetExternalTwoEnded) :
    Equates occurrence after targetCanonical targetExternalTwoEnded := by
  have optional : ∀ {first last : OpenDiagram boundary},
      Relation.TransGen Step first last →
        Relation.ReflTransGen Step first last := by
    intro first last steps
    induction steps with
    | single step => exact .tail .refl step
    | tail steps step induction => exact .tail induction step
  exact ⟨optional strict.1, optional strict.2⟩

/-- A nonempty symmetric loop at an exact occurrence. The two Vacuity steps
insert and immediately remove one structurally fixed point, so presentation
transport never relies on a zero-length derivation. -/
theorem StrictEquates.refl
    {boundary holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source) :
    StrictEquates occurrence before occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded := by
  have regionEta :
      Vacuity.Point.plain before.locals before.items = before := by
    cases before
    rfl
  let pointOccurrence : Occurrence
      (Vacuity.Point.plain before.locals before.items) source := by
    rw [regionEta]
    exact occurrence
  have pointValidity :=
    Vacuity.Point.introduceValidity pointOccurrence Sig.iota
  let pointEndpoint := pointOccurrence.interface.withBody
    (pointOccurrence.context.fill
      (Vacuity.Point.present before.locals before.items Sig.iota))
    pointValidity.1 pointValidity.2
  have introduction : Vacuity source pointEndpoint := by
    exact ⟨holeWires,
      Vacuity.Point.plain before.locals before.items,
      Vacuity.Point.present before.locals before.items Sig.iota,
      pointOccurrence, pointValidity.1, pointValidity.2,
      OpenDiagramIso.refl _,
      atPolarity_symmetric_of pointOccurrence.context.polarity
        (.mk (.point before.locals before.items Sig.iota))⟩
  let exact := occurrence.interface.withBody
    (occurrence.context.fill before) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have exactIntroduction : Vacuity exact pointEndpoint := by
    exact Vacuity.iso occurrence.host_iso introduction
      (OpenDiagramIso.refl pointEndpoint)
  exact ⟨(Relation.TransGen.single (Step.vacuity introduction)).tail
      (Step.vacuity exactIntroduction.symm),
    (Relation.TransGen.single (Step.vacuity exactIntroduction)).tail
      (Step.vacuity introduction.symm)⟩

/-- Transport the exact target presentation of a nonempty symmetric phase. -/
theorem StrictEquates.targetIso
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (strict : StrictEquates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (targetIso : OpenDiagramIso
      (occurrence.interface.withBody (occurrence.context.fill middle)
        middleCanonical middleExternalTwoEnded)
      (occurrence.interface.withBody (occurrence.context.fill after)
        targetCanonical targetExternalTwoEnded)) :
    StrictEquates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨transGen_iso (OpenDiagramIso.refl source) strict.1 targetIso,
    transGen_iso targetIso strict.2 (OpenDiagramIso.refl source)⟩

/-- Consecutive nonempty symmetric phases compose at their exact midpoint. -/
theorem StrictEquates.trans
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (first : StrictEquates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (second : StrictEquates
      (exactOccurrence occurrence.interface occurrence.context middle
        middleCanonical middleExternalTwoEnded)
      after targetCanonical targetExternalTwoEnded) :
    StrictEquates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨first.1.trans second.1, second.2.trans first.2⟩

/-- Consecutive bidirectional phases at the same actual occurrence compose. -/
theorem Equates.trans
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)}
    (first : Equates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (second : Equates
      (exactOccurrence occurrence.interface occurrence.context middle
        middleCanonical middleExternalTwoEnded)
      after targetCanonical targetExternalTwoEnded) :
    Equates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨first.1.trans second.1, second.2.trans first.2⟩

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

end VisualProof.Rule.Completeness
