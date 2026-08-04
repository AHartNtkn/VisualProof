import VisualProof.Rule.Soundness.Comprehension.AbstractionTrace

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

namespace AbstractionRawTrace

@[simp] theorem region_survives_iff
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (region : Fin input.val.regionCount) :
    (Domains input occurrences).regions.survives region = true ↔
      region ∉ abstractionRegions occurrences := by
  simp [Domains, abstractionDomains, AbstractionDomains.regions_exact]

@[simp] theorem node_survives_iff
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (node : Fin input.val.nodeCount) :
    (Domains input occurrences).nodes.survives node = true ↔
      node ∉ abstractionNodes occurrences := by
  simp [Domains, abstractionDomains, AbstractionDomains.nodes_exact]

@[simp] theorem wire_survives_iff
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (wire : Fin input.val.wireCount) :
    (Domains input occurrences).wires.survives wire = true ↔
      wire ∉ abstractionWires occurrences := by
  simp [Domains, abstractionDomains, AbstractionDomains.wires_exact]

theorem selection_anchor_not_selected
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    selection.val.anchor ∉ selection.selectedRegions := by
  intro selected
  obtain ⟨child, childRoot, enclosed⟩ :=
    (selection.mem_selectedRegions selection.val.anchor).1 selected
  exact ConcreteElaboration.checked_direct_child_not_encloses_parent
    input.property (selection.property.childRoots_direct child childRoot)
      enclosed

theorem occurrence_anchor_not_abstractionRegions
    (payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (index : Fin occurrences.length) :
    (occurrences.get index).selection.val.anchor ∉
      abstractionRegions occurrences := by
  intro selected
  rw [abstractionRegions, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, regionMember⟩ := selected
  obtain ⟨other, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at regionMember
  by_cases same : index = other
  · subst other
    exact selection_anchor_not_selected input (occurrences.get index).selection
      regionMember
  · exact payload.anchors_not_nested index other same regionMember

theorem occurrence_anchor_survives
    (payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (index : Fin occurrences.length) :
    (Domains input occurrences).regions.survives
        (occurrences.get index).selection.val.anchor = true :=
  (region_survives_iff input occurrences _).2
    (occurrence_anchor_not_abstractionRegions payload index)

theorem wrap_anchor_not_abstractionRegions
    (payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences) :
    wrap.val.anchor ∉ abstractionRegions occurrences := by
  intro selected
  rw [abstractionRegions, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, regionMember⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at regionMember
  exact selection_anchor_not_selected input wrap
    (payload.regions_inside index wrap.val.anchor regionMember)

theorem wrap_anchor_survives
    (payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences) :
    (Domains input occurrences).regions.survives wrap.val.anchor = true :=
  (region_survives_iff input occurrences _).2
    (wrap_anchor_not_abstractionRegions payload)

/-- Compact target identifier of one surviving original region. -/
def targetRegion
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true) :
    Fin trace.diagram.regionCount :=
  Fin.castSucc (trace.domains.regions.index region survives)

/-- Compact target identifier of one surviving original node. -/
def targetNode
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true) :
    Fin trace.diagram.nodeCount :=
  Fin.castAdd occurrences.length (trace.domains.nodes.index node survives)

/-- Compact target identifier of one surviving original wire. -/
def targetWire
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin input.val.wireCount)
    (survives : trace.domains.wires.survives wire = true) :
    Fin trace.diagram.wireCount :=
  trace.domains.wires.index wire survives

/-- Fresh relation atom belonging to one certified occurrence. -/
def targetAtom
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (index : Fin occurrences.length) : Fin trace.diagram.nodeCount :=
  Fin.natAdd trace.domains.nodes.count index

@[simp] theorem targetRegion_origin
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true) :
    trace.domains.regions.origin
        (trace.domains.regions.index region survives) = region :=
  trace.domains.regions.origin_index region survives

@[simp] theorem targetNode_origin
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true) :
    trace.domains.nodes.origin
        (trace.domains.nodes.index node survives) = node :=
  trace.domains.nodes.origin_index node survives

@[simp] theorem targetWire_origin
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin input.val.wireCount)
    (survives : trace.domains.wires.survives wire = true) :
    trace.domains.wires.origin
        (trace.domains.wires.index wire survives) = wire :=
  trace.domains.wires.origin_index wire survives

theorem root_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    trace.domains.regions.survives input.val.root = true := by
  rw [← trace.root_origin]
  exact trace.domains.regions.origin_survives trace.rootBase

@[simp] theorem targetRegion_root
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    trace.targetRegion input.val.root
        trace.root_survives =
      trace.diagram.root := by
  unfold targetRegion
  have indexed := trace.domains.regions.index?_index input.val.root
    trace.root_survives
  rw [trace.root_result] at indexed
  exact congrArg Fin.castSucc (Option.some.inj indexed).symm

theorem atomOwner_eq_bubble_of_anchor_eq
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (index : Fin occurrences.length)
    (anchor : (occurrences.get index).selection.val.anchor = wrap.val.anchor) :
    trace.atomOwners index = trace.bubble := by
  have result := trace.atomOwner_result index
  simp only [anchor, if_pos, Option.some.injEq] at result
  exact result.symm

theorem atomOwner_eq_targetRegion_of_anchor_ne
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (index : Fin occurrences.length)
    (anchor : (occurrences.get index).selection.val.anchor ≠ wrap.val.anchor) :
    trace.atomOwners index = trace.targetRegion
        (occurrences.get index).selection.val.anchor
        (occurrence_anchor_survives payload index) := by
  have result := trace.atomOwner_result index
  simp only [anchor, if_neg] at result
  rw [trace.domains.regions.index?_index _
    (occurrence_anchor_survives payload index)] at result
  exact (Option.some.inj result).symm

theorem abstractRegion?_targetRegion
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true) :
    abstractRegion? input wrap occurrences trace.domains trace.bubble region =
      some (trace.diagram.regions (trace.targetRegion region survives)) := by
  have result := trace.region_result
    (trace.domains.regions.index region survives)
  rw [trace.domains.regions.origin_index region survives] at result
  simpa only [targetRegion, diagram_survivorRegion] using result

theorem abstractNode?_targetNode
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true) :
    abstractNode? input wrap occurrences trace.domains trace.bubble node =
      some (trace.diagram.nodes (trace.targetNode node survives)) := by
  have result := trace.node_result
    (trace.domains.nodes.index node survives)
  rw [trace.domains.nodes.origin_index node survives] at result
  simpa only [targetNode, diagram_survivorNode] using result

theorem abstractWire?_targetWire
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin input.val.wireCount)
    (survives : trace.domains.wires.survives wire = true) :
    (do
      let scopeBase ← trace.domains.regions.index?
        (input.val.wires wire).scope
      pure {
        scope := scopeBase.castSucc
        endpoints := abstractFrameEndpoints input occurrences trace.domains
            (trace.domains.wires.index wire survives) ++
          abstractAtomEndpoints input occurrences trace.domains
            (trace.domains.wires.index wire survives)
      }) = some (trace.diagram.wires (trace.targetWire wire survives)) := by
  have result := trace.wire_result
    (trace.domains.wires.index wire survives)
  rw [trace.domains.wires.origin_index wire survives] at result
  simpa only [targetWire, diagram_wire] using result

end AbstractionRawTrace

end VisualProof.Rule
