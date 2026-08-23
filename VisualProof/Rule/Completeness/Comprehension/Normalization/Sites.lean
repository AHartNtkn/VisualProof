import VisualProof.Rule.Completeness.Comprehension.Normalization.Arguments

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

/-- The fixed traversal frame retains the exact source-side instantiation
indices and uses the identity target context only as an inert site annotation
index. -/
def normalizationFrame (outer before after arguments : List Sig) :
    Transform.Frame arguments (outer ++ (before ++ after))
      (outer ++ (before ++ .rel arguments :: after))
      (outer ++ (before ++ after)) where
  sourceKeep := _root_.VisualProof.Rule.Comprehension.retain outer before after
    arguments
  targetKeep := WireRenaming.id
  selected := _root_.VisualProof.Rule.Comprehension.selected outer before after
    arguments

mutual
  /-- Unit site annotations exist for every exact authoritative region
  result. The existential stays in `Prop`, so no Instantiation proof is
  eliminated into caller-selectable data. -/
  theorem normalizationRegionSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | mk itemsEvidence =>
        obtain ⟨sites⟩ := normalizationItemsSites_nonempty
          (frame := frame.append _) itemsEvidence
        exact ⟨.mk sites⟩
  termination_by sizeOf source

  /-- Unit site annotations exist for every exact authoritative item-sequence
  result. -/
  theorem normalizationItemsSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := normalizationItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := normalizationItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  /-- Unit site annotations exist for every exact authoritative item result. -/
  theorem normalizationItemSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | atom head ports =>
        exact ⟨ItemSites.atom (pattern := pattern) (frame := frame) head ports⟩
    | selectedAtom ports =>
        exact ⟨ItemSites.selectedAtom (pattern := pattern) (frame := frame)
          ports PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨ItemSites.identity (pattern := pattern) (frame := frame)
          signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨sites⟩ := normalizationRegionSites_nonempty childEvidence
        exact ⟨.cut sites⟩
  termination_by sizeOf source
end

/-- A fixed unit-data site traversal selected internally from exact
Instantiation evidence. -/
noncomputable def normalizationSites
    {arguments common sourceWires targetWires : List Sig}
    {pattern : OpenDiagram arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result) :
    ItemsSites (normalizationOperation arguments) PUnit.unit evidence :=
  Classical.choice (normalizationItemsSites_nonempty evidence)

end VisualProof.Rule.Completeness.Comprehension
