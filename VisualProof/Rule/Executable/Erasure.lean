import VisualProof.Rule.Erasure

namespace VisualProof.Rule.Erasure

open Theory
open Diagram

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | erase
      (hostLocals : List Sig)
      (hostItems : ItemSeq (holeWires ++ hostLocals))
      (material : Region materialWires)
      (wireMap : WireRenaming materialWires (holeWires ++ hostLocals))
      (occurrence : Occurrence
        (Region.spliceAt hostLocals hostItems material wireMap) source)
      (polarity : occurrence.context.polarity = .positive) :
      ForwardIndex source
  | insert
      (hostLocals : List Sig)
      (hostItems : ItemSeq (holeWires ++ hostLocals))
      (material : Region materialWires)
      (wireMap : WireRenaming materialWires (holeWires ++ hostLocals))
      (occurrence : Occurrence
        (eraseAt hostLocals hostItems material wireMap) source)
      (polarity : occurrence.context.polarity = .negative)
      (targetCanonical : (occurrence.context.fill
        (Region.spliceAt hostLocals hostItems material wireMap)).Canonical) :
      ForwardIndex source

inductive BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | insert
      (hostLocals : List Sig)
      (hostItems : ItemSeq (holeWires ++ hostLocals))
      (material : Region materialWires)
      (wireMap : WireRenaming materialWires (holeWires ++ hostLocals))
      (occurrence : Occurrence
        (eraseAt hostLocals hostItems material wireMap) source)
      (polarity : occurrence.context.polarity = .positive)
      (targetCanonical : (occurrence.context.fill
        (Region.spliceAt hostLocals hostItems material wireMap)).Canonical) :
      BackwardIndex source
  | erase
      (hostLocals : List Sig)
      (hostItems : ItemSeq (holeWires ++ hostLocals))
      (material : Region materialWires)
      (wireMap : WireRenaming materialWires (holeWires ++ hostLocals))
      (occurrence : Occurrence
        (Region.spliceAt hostLocals hostItems material wireMap) source)
      (polarity : occurrence.context.polarity = .negative) :
      BackwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary
  | .erase hostLocals hostItems material wireMap occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill
        (eraseAt hostLocals hostItems material wireMap))
        (occurrenceTargetCanonical hostLocals hostItems material wireMap
          occurrence)
        (occurrenceTargetExternalTwoEnded hostLocals hostItems material
          wireMap occurrence)
  | .insert hostLocals hostItems material wireMap occurrence _
      targetCanonical =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocals hostItems material wireMap))
        targetCanonical
        (occurrenceInsertedExternalTwoEnded hostLocals hostItems material
          wireMap occurrence targetCanonical)

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary
  | .insert hostLocals hostItems material wireMap occurrence _
      targetCanonical =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (Region.spliceAt hostLocals hostItems material wireMap))
        targetCanonical
        (occurrenceInsertedExternalTwoEnded hostLocals hostItems material
          wireMap occurrence targetCanonical)
  | .erase hostLocals hostItems material wireMap occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (eraseAt hostLocals hostItems material wireMap))
        (occurrenceTargetCanonical hostLocals hostItems material wireMap
          occurrence)
        (occurrenceTargetExternalTwoEnded hostLocals hostItems material
          wireMap occurrence)

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
    Rule.Erasure source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | erase hostLocals hostItems material wireMap occurrence polarity =>
        refine ⟨_, _, _, occurrence,
          occurrenceTargetCanonical hostLocals hostItems material wireMap
            occurrence,
          occurrenceTargetExternalTwoEnded hostLocals hostItems material
            wireMap occurrence,
          OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        exact Local.erase hostLocals hostItems material wireMap
    | insert hostLocals hostItems material wireMap occurrence polarity
        targetCanonical =>
        refine ⟨_, _, _, occurrence, targetCanonical,
          occurrenceInsertedExternalTwoEnded hostLocals hostItems material
            wireMap occurrence targetCanonical,
          OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        exact Local.erase hostLocals hostItems material wireMap
  · rintro ⟨wires, before, after, occurrence, targetCanonical,
      targetExternalTwoEnded, targetIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity] at localEvidence
        cases localEvidence with
        | erase hostLocals hostItems material wireMap =>
            exact ⟨.erase hostLocals hostItems material wireMap occurrence
              polarity, ⟨targetIso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, converse] at localEvidence
        cases localEvidence with
        | erase hostLocals hostItems material wireMap =>
            exact ⟨.insert hostLocals hostItems material wireMap occurrence
              polarity targetCanonical, ⟨targetIso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
    Rule.Erasure target source := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply backward_respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | insert hostLocals hostItems material wireMap occurrence polarity
        targetCanonical =>
        let outputOccurrence : Occurrence
            (Region.spliceAt hostLocals hostItems material wireMap)
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Region.spliceAt hostLocals hostItems material wireMap))
              targetCanonical
              (occurrenceInsertedExternalTwoEnded hostLocals hostItems
                material wireMap occurrence targetCanonical)) := {
          interface := occurrence.interface
          context := occurrence.context
          sourceCanonical := targetCanonical
          sourceExternalTwoEnded := occurrenceInsertedExternalTwoEnded
            hostLocals hostItems material wireMap occurrence targetCanonical
          host_iso := OpenDiagramIso.refl _
        }
        refine ⟨_, _, _, outputOccurrence, occurrence.sourceCanonical,
          occurrence.sourceExternalTwoEnded,
          occurrence.host_iso, ?_⟩
        rw [polarity]
        exact Local.erase hostLocals hostItems material wireMap
    | erase hostLocals hostItems material wireMap occurrence polarity =>
        let outputCanonical := occurrenceTargetCanonical hostLocals hostItems
          material wireMap occurrence
        let outputOccurrence : Occurrence
            (eraseAt hostLocals hostItems material wireMap)
            (occurrence.interface.withBody
              (occurrence.context.fill
                (eraseAt hostLocals hostItems material wireMap))
              outputCanonical
              (occurrenceTargetExternalTwoEnded hostLocals hostItems
                material wireMap occurrence)) := {
          interface := occurrence.interface
          context := occurrence.context
          sourceCanonical := outputCanonical
          sourceExternalTwoEnded := occurrenceTargetExternalTwoEnded
            hostLocals hostItems material wireMap occurrence
          host_iso := OpenDiagramIso.refl _
        }
        refine ⟨_, _, _, outputOccurrence, occurrence.sourceCanonical,
          occurrence.sourceExternalTwoEnded,
          occurrence.host_iso, ?_⟩
        rw [polarity]
        exact Local.erase hostLocals hostItems material wireMap
  · rintro ⟨wires, before, after, occurrence, targetCanonical,
      targetExternalTwoEnded, sourceIso, localEvidence⟩
    cases polarity : occurrence.context.polarity with
    | positive =>
        simp only [polarity, atPolarity] at localEvidence
        cases localEvidence with
        | erase hostLocals hostItems material wireMap =>
            let sourceOccurrence : Occurrence
                (eraseAt hostLocals hostItems material wireMap) source := {
              interface := occurrence.interface
              context := occurrence.context
              sourceCanonical := targetCanonical
              sourceExternalTwoEnded := targetExternalTwoEnded
              host_iso := sourceIso
            }
            exact ⟨.insert hostLocals hostItems material wireMap
              sourceOccurrence polarity occurrence.sourceCanonical,
              ⟨occurrence.host_iso.symm⟩⟩
    | negative =>
        simp only [polarity, atPolarity, converse] at localEvidence
        cases localEvidence with
        | erase hostLocals hostItems material wireMap =>
            let sourceOccurrence : Occurrence
                (Region.spliceAt hostLocals hostItems material wireMap)
                source := {
              interface := occurrence.interface
              context := occurrence.context
              sourceCanonical := targetCanonical
              sourceExternalTwoEnded := targetExternalTwoEnded
              host_iso := sourceIso
            }
            exact ⟨.erase hostLocals hostItems material wireMap
              sourceOccurrence polarity, ⟨occurrence.host_iso.symm⟩⟩

end VisualProof.Rule.Erasure
