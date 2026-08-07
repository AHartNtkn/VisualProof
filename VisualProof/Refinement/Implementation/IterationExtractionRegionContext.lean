import VisualProof.Refinement.Implementation.IterationExtractionRegionOccurrence

namespace VisualProof.Refinement.Implementation.IterationExtraction

open VisualProof.Concrete
open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

theorem extractionContextMembership_extend_material
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (ambient : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (material : Fin layout.materialRegionCount)
    (wire : Fin layout.wireCount) :
    input.val.fragmentWireOrigin selection layout wire ∈
        hostContext.extend (selection.selectedRegions.get material) ↔
      wire ∈ fragmentContext.extend (layout.materialRegion material) := by
  constructor
  · intro member
    rcases List.mem_append.mp member with ambientMember | localMember
    · exact List.mem_append.mpr (Or.inl ((ambient wire).1 ambientMember))
    · exact List.mem_append.mpr (Or.inr
        ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
          layout wire material).2 localMember))
  · intro member
    rcases List.mem_append.mp member with ambientMember | localMember
    · exact List.mem_append.mpr (Or.inl ((ambient wire).2 ambientMember))
    · exact List.mem_append.mpr (Or.inr
        ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
          layout wire material).1 localMember))

noncomputable def extractionContextIndexMapOfMembership
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext) :
    Fin fragmentContext.length → Fin hostContext.length :=
  fun index => Classical.choose (indexOf?_complete ((membership _).2
    (List.get_mem fragmentContext index)))

theorem extractionContextIndexMapOfMembership_spec
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (index : Fin fragmentContext.length) :
    input.val.fragmentWireOrigin selection layout
        (fragmentContext.get index) =
      hostContext.get
        (extractionContextIndexMapOfMembership input selection layout
          fragmentContext hostContext membership index) := by
  unfold extractionContextIndexMapOfMembership
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((membership _).2 (List.get_mem fragmentContext index)))) |>.symm

theorem extractionResolvePort_mapOfMembership
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (hostNodup : hostContext.Nodup)
    (node : Fin layout.nodeCount)
    (port : CPort) :
    Concrete.Elaboration.resolvePort? input.val hostContext
        (selection.selectedNodes.get node) port =
      (Concrete.Elaboration.resolvePort?
        (input.val.extractDiagramRaw selection layout) fragmentContext node port
      ).map (extractionContextIndexMapOfMembership input selection layout
        fragmentContext hostContext membership) := by
  apply Concrete.Elaboration.resolvePort?_map_of_occurrence
    fragmentContext hostContext node (selection.selectedNodes.get node)
    (input.val.fragmentWireOrigin selection layout)
    (extractionContextIndexMapOfMembership input selection layout
      fragmentContext hostContext membership) hostNodup
  · intro index
    exact (extractionContextIndexMapOfMembership_spec input selection layout
      fragmentContext hostContext membership index).symm
  · exact membership
  · intro wire requested occurs
    obtain ⟨original, originalOccurs, mapped⟩ :=
      (input.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout wire
        ⟨node, requested⟩).1 occurs
    rw [Concrete.Diagram.fragmentEndpoint?_origin selection mapped] at originalOccurs
    exact originalOccurs
  · intro hostWire requested occurs
    obtain ⟨fragmentWire, fragmentOccurs⟩ :=
      Concrete.Diagram.extractDiagramRaw_endpointOccurs_of_selected input
        selection layout node requested occurs
    refine ⟨fragmentWire, ?_, fragmentOccurs⟩
    obtain ⟨original, originalOccurs, mapped⟩ :=
      (input.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
        fragmentWire ⟨node, requested⟩).1 fragmentOccurs
    rw [Concrete.Diagram.fragmentEndpoint?_origin selection mapped] at originalOccurs
    exact Concrete.Elaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint originalOccurs occurs
  · exact input.property.wire_endpoints_are_disjoint

end VisualProof.Refinement.Implementation.IterationExtraction
