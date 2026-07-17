import VisualProof.Rule.Soundness.Iteration.ExtractionRegionOccurrence

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- Exact provenance agreement of ambient contexts is preserved when both
compilers descend into corresponding copied material. -/
theorem extractionContextMembership_extend_material
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
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
    · apply List.mem_append.mpr
      exact Or.inl ((ambient wire).1 ambientMember)
    · apply List.mem_append.mpr
      exact Or.inr
        ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
          layout wire material).2 localMember)
  · intro member
    rcases List.mem_append.mp member with ambientMember | localMember
    · apply List.mem_append.mpr
      exact Or.inl ((ambient wire).2 ambientMember)
    · apply List.mem_append.mpr
      exact Or.inr
        ((fragmentWireOrigin_mem_exactScopeWires_material_iff input selection
          layout wire material).1 localMember)

/-- Canonical lexical index transport from any pair of contexts known to
contain exactly the same provenance wires. -/
noncomputable def extractionContextIndexMapOfMembership
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext) :
    Fin fragmentContext.length → Fin hostContext.length :=
  fun index => Classical.choose (indexOf?_complete ((membership _).2
    (List.get_mem fragmentContext index)))

theorem extractionContextIndexMapOfMembership_spec
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (index : Fin fragmentContext.length) :
    (extractionContextRelation input selection layout fragmentContext
      hostContext).Rel index
        (extractionContextIndexMapOfMembership input selection layout
          fragmentContext hostContext membership index) := by
  unfold extractionContextRelation extractionContextIndexMapOfMembership
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((membership _).2 (List.get_mem fragmentContext index)))) |>.symm

theorem extractionContextEnvironmentsAgreeOfMembership
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (hostNodup : hostContext.Nodup)
    (hostEnv : Fin hostContext.length → D) :
    (extractionContextRelation input selection layout fragmentContext
      hostContext).EnvironmentsAgree
        (hostEnv ∘ extractionContextIndexMapOfMembership input selection layout
          fragmentContext hostContext membership)
        hostEnv := by
  intro fragmentIndex hostIndex related
  have chosen := extractionContextIndexMapOfMembership_spec input selection
    layout fragmentContext hostContext membership fragmentIndex
  unfold extractionContextRelation at related chosen
  apply congrArg hostEnv
  apply Fin.ext
  exact (List.getElem_inj hostNodup).mp (by
    simpa only [List.get_eq_getElem] using chosen.symm.trans related)

/-- Port resolution transports through any recursively corresponding pair of
contexts; terminal exactness is only one way to establish membership equality. -/
theorem extractionResolvePort_mapOfMembership
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (hostNodup : hostContext.Nodup)
    (node : Fin layout.nodeCount)
    (port : CPort) :
    ConcreteElaboration.resolvePort? input.val hostContext
        (selection.selectedNodes.get node) port =
      (ConcreteElaboration.resolvePort?
        (input.val.extractDiagramRaw selection layout) fragmentContext node port
      ).map (extractionContextIndexMapOfMembership input selection layout
        fragmentContext hostContext membership) := by
  apply ConcreteElaboration.resolvePort?_map_of_occurrence
    fragmentContext hostContext node (selection.selectedNodes.get node)
    (input.val.fragmentWireOrigin selection layout)
    (extractionContextIndexMapOfMembership input selection layout
      fragmentContext hostContext membership)
    hostNodup
  · intro index
    exact (extractionContextIndexMapOfMembership_spec input selection layout
      fragmentContext hostContext membership index).symm
  · exact membership
  · intro wire requested occurs
    obtain ⟨original, originalOccurs, mapped⟩ :=
      (input.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout wire
        ⟨node, requested⟩).1 occurs
    rw [ConcreteDiagram.fragmentEndpoint?_origin selection mapped] at originalOccurs
    exact originalOccurs
  · intro hostWire requested occurs
    obtain ⟨fragmentWire, fragmentOccurs⟩ :=
      ConcreteDiagram.extractDiagramRaw_endpointOccurs_of_selected input
        selection layout node requested occurs
    refine ⟨fragmentWire, ?_, fragmentOccurs⟩
    obtain ⟨original, originalOccurs, mapped⟩ :=
      (input.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
        fragmentWire ⟨node, requested⟩).1 fragmentOccurs
    rw [ConcreteDiagram.fragmentEndpoint?_origin selection mapped] at originalOccurs
    exact ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint originalOccurs occurs
  · exact input.property.wire_endpoints_are_disjoint

theorem extractionResolvePort_relatedOfMembership
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (hostNodup : hostContext.Nodup)
    (node : Fin layout.nodeCount)
    (port : CPort)
    (fragmentIndex : Fin fragmentContext.length)
    (hostIndex : Fin hostContext.length)
    (fragmentResolved : ConcreteElaboration.resolvePort?
      (input.val.extractDiagramRaw selection layout) fragmentContext node port =
        some fragmentIndex)
    (hostResolved : ConcreteElaboration.resolvePort? input.val hostContext
      (selection.selectedNodes.get node) port = some hostIndex) :
    (extractionContextRelation input selection layout fragmentContext
      hostContext).Rel fragmentIndex hostIndex := by
  have mapped := extractionResolvePort_mapOfMembership input selection layout
    fragmentContext hostContext membership hostNodup node port
  rw [fragmentResolved, hostResolved] at mapped
  have indexEq := Option.some.inj mapped.symm
  subst hostIndex
  exact extractionContextIndexMapOfMembership_spec input selection layout
    fragmentContext hostContext membership fragmentIndex

end VisualProof.Rule.IterationSoundness
