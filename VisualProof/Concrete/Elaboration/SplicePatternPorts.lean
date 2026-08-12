import VisualProof.Concrete.Elaboration.SpliceFramePorts


namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Elaboration

namespace Splice.Input.PlugLayout

/-- The stable exposed-class position of an exposed pattern wire. -/
noncomputable def exposedWireIndex (_layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (exposed : wire ∈ input.pattern.val.exposedWires) :
    Fin input.pattern.val.exposedWires.length :=
  (indexOf? input.pattern.val.exposedWires wire).get (by
    rw [indexOf?_isSome_iff]
    exact exposed)

theorem exposedWires_get_exposedWireIndex (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (exposed : wire ∈ input.pattern.val.exposedWires) :
    input.pattern.val.exposedWires.get
        (layout.exposedWireIndex wire exposed) = wire := by
  unfold exposedWireIndex
  let present :
      (indexOf? input.pattern.val.exposedWires wire).isSome = true := by
    rw [indexOf?_isSome_iff]
    exact exposed
  obtain ⟨index, found⟩ := Option.isSome_iff_exists.mp present
  rw [show (indexOf? input.pattern.val.exposedWires wire).get present =
      index from Option.get_of_eq_some present found]
  exact indexOf?_sound found

theorem exposedWireIndex_get (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    layout.exposedWireIndex
        (input.pattern.val.exposedWires.get external)
        (List.get_mem input.pattern.val.exposedWires external) = external := by
  unfold exposedWireIndex
  exact Option.get_of_eq_some _
    (indexOf?_get_eq_some_of_nodup
      input.pattern.val.exposedWires_nodup external)

/-- Total source-derived pattern-wire transport into the raw plug carrier.
Exposed classes use their canonical attachment; every other wire uses its
dense internal survivor identifier. -/
theorem patternWireMap_of_exposed (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (exposed : wire ∈ input.pattern.val.exposedWires) :
    layout.patternWireMap wire =
      layout.frameWire
        (layout.exposedAttachment (layout.exposedWireIndex wire exposed)) := by
  unfold patternWireMap
  simp only [dif_pos exposed]
  congr 2

theorem patternWireMap_of_internal (layout : PlugLayout input)
    (internal : layout.internalWires.Carrier) :
    layout.patternWireMap (layout.internalWires.origin internal) =
      layout.internalWire internal := by
  have notExposed : layout.internalWires.origin internal ∉
      input.pattern.val.exposedWires := by
    have survives := layout.internalWires.origin_survives internal
    rw [layout.internalWires_exact] at survives
    exact decide_eq_true_iff.mp survives
  unfold patternWireMap
  rw [dif_neg notExposed]
  congr 1
  exact layout.internalWires.index_origin internal

/-- Exposed class transport computes to its canonical attached quotient wire. -/
theorem patternWireMap_exposed_get (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    layout.patternWireMap (input.pattern.val.exposedWires.get external) =
      layout.frameWire (layout.exposedAttachment external) := by
  have exposed : input.pattern.val.exposedWires.get external ∈
      input.pattern.val.exposedWires := List.get_mem _ _
  rw [layout.patternWireMap_of_exposed _ exposed,
    layout.exposedWireIndex_get external]

theorem patternNode_injective (layout : PlugLayout input) :
    Function.Injective layout.patternNode := by
  intro left right equality
  apply Fin.ext
  have values := congrArg Fin.val equality
  simpa [patternNode] using values

theorem internalWire_injective (layout : PlugLayout input) :
    Function.Injective layout.internalWire := by
  intro left right equality
  apply Fin.ext
  have values := congrArg Fin.val equality
  simpa [internalWire] using values

private theorem frameNode_ne_patternNode (layout : PlugLayout input)
    (frame : Fin input.frame.val.nodeCount)
    (pattern : Fin input.pattern.val.diagram.nodeCount) :
    layout.frameNode frame ≠ layout.patternNode pattern := by
  intro equality
  have values := congrArg Fin.val equality
  simp [frameNode, patternNode] at values
  omega

private theorem mapPatternEndpoint_eq_iff (layout : PlugLayout input)
    (endpoint : CEndpoint input.pattern.val.diagram.nodeCount)
    (node : Fin input.pattern.val.diagram.nodeCount) (port : CPort) :
    layout.mapPatternEndpoint endpoint =
        ⟨layout.patternNode node, port⟩ ↔
      endpoint = ⟨node, port⟩ := by
  constructor
  · intro equality
    obtain ⟨sourceNode, sourcePort⟩ := endpoint
    have nodeEq : sourceNode = node := layout.patternNode_injective
      (congrArg CEndpoint.node equality)
    have portEq : sourcePort = port := congrArg CEndpoint.port equality
    subst sourceNode
    subst sourcePort
    rfl
  · rintro rfl
    rfl

theorem endpointOccurs_patternNode_forward (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (node : Fin input.pattern.val.diagram.nodeCount) (port : CPort)
    (occurs : input.pattern.val.diagram.EndpointOccurs wire ⟨node, port⟩) :
    layout.plugRaw.EndpointOccurs (layout.patternWireMap wire)
      ⟨layout.patternNode node, port⟩ := by
  by_cases exposed : wire ∈ input.pattern.val.exposedWires
  · rw [layout.patternWireMap_of_exposed wire exposed]
    simp only [Diagram.EndpointOccurs, plugRaw, plugWire, frameWire,
      Fin.addCases_left]
    apply List.mem_append_right
    unfold boundaryEndpoints
    apply List.mem_map.mpr
    refine ⟨⟨node, port⟩, ?_, rfl⟩
    rw [List.mem_flatMap]
    refine ⟨wire, ?_, occurs⟩
    unfold boundaryWires
    apply List.mem_map.mpr
    refine ⟨layout.exposedWireIndex wire exposed, ?_, ?_⟩
    · simp [exposedAttachment]
    · exact layout.exposedWires_get_exposedWireIndex wire exposed
  · let internal := layout.internalWires.index wire (by
      rw [layout.internalWires_exact]
      exact decide_eq_true_iff.mpr exposed)
    have origin : layout.internalWires.origin internal = wire := by
      exact layout.internalWires.origin_index wire _
    rw [← origin, layout.patternWireMap_internal]
    simp only [Diagram.EndpointOccurs, plugRaw, plugWire, internalWire,
      Fin.addCases_right, mapPatternWire]
    apply List.mem_map.mpr
    refine ⟨⟨node, port⟩, ?_, rfl⟩
    change input.pattern.val.diagram.EndpointOccurs
      (layout.internalWires.origin internal) ⟨node, port⟩
    rw [origin]
    exact occurs

/-- Every endpoint at a transported pattern node in the raw plug comes from
one source pattern wire whose total carrier image is the target wire. -/
theorem endpointOccurs_patternNode_backward (layout : PlugLayout input)
    (targetWire : Fin layout.plugRaw.wireCount)
    (node : Fin input.pattern.val.diagram.nodeCount) (port : CPort)
    (occurs : layout.plugRaw.EndpointOccurs targetWire
      ⟨layout.patternNode node, port⟩) :
    ∃ sourceWire : Fin input.pattern.val.diagram.wireCount,
      layout.patternWireMap sourceWire = targetWire ∧
        input.pattern.val.diagram.EndpointOccurs sourceWire ⟨node, port⟩ := by
  revert occurs
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun quotient occurs => ?_)
      (fun internal occurs => ?_) targetWire
  · simp only [Diagram.EndpointOccurs, plugRaw, plugWire,
      Fin.addCases_left] at occurs
    rcases List.mem_append.mp occurs with frameEndpoint | patternEndpoint
    · obtain ⟨endpoint, _, mapped⟩ := List.mem_map.mp frameEndpoint
      exact False.elim (layout.frameNode_ne_patternNode endpoint.node node
        (congrArg CEndpoint.node mapped))
    · unfold boundaryEndpoints at patternEndpoint
      obtain ⟨endpoint, endpointMember, mapped⟩ :=
        List.mem_map.mp patternEndpoint
      rw [List.mem_flatMap] at endpointMember
      obtain ⟨sourceWire, boundaryMember, sourceOccurs⟩ := endpointMember
      unfold boundaryWires at boundaryMember
      obtain ⟨external, externalMember, sourceEq⟩ :=
        List.mem_map.mp boundaryMember
      have attachmentEq : layout.exposedAttachment external = quotient := by
        simpa using (List.mem_filter.mp externalMember).2
      subst sourceWire
      have exposed : input.pattern.val.exposedWires.get external ∈
          input.pattern.val.exposedWires := by
        exact List.get_mem _ _
      have externalEq : layout.exposedWireIndex
          (input.pattern.val.exposedWires.get external) exposed = external := by
        exact layout.exposedWireIndex_get external
      refine ⟨input.pattern.val.exposedWires.get external, ?_, ?_⟩
      · rw [layout.patternWireMap_of_exposed
            (input.pattern.val.exposedWires.get external) exposed,
          externalEq, attachmentEq]
        rfl
      · have endpointEq : endpoint = ⟨node, port⟩ :=
          (layout.mapPatternEndpoint_eq_iff endpoint node port).1 mapped
        simpa [endpointEq] using sourceOccurs
  · simp only [Diagram.EndpointOccurs, plugRaw, plugWire,
      Fin.addCases_right, mapPatternWire] at occurs
    obtain ⟨endpoint, sourceOccurs, mapped⟩ := List.mem_map.mp occurs
    have endpointEq : endpoint = ⟨node, port⟩ :=
      (layout.mapPatternEndpoint_eq_iff endpoint node port).1 mapped
    refine ⟨layout.internalWires.origin internal,
      layout.patternWireMap_internal internal, ?_⟩
    simpa [endpointEq] using sourceOccurs

/-- Resolve one transported pattern-node port in an exact target context from
the concrete pattern-wire map and its position map. Aliased exposed wires are
allowed; target-context nodup identifies their shared lexical position. -/
theorem resolvePort?_patternNode_map (layout : PlugLayout input)
    (sourceParent : Fin input.pattern.val.diagram.regionCount)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (sourceExact : sourceContext.Exact sourceParent)
    (targetNodup : targetContext.Nodup)
    (getMapped : ∀ index,
      targetContext.get (indexMap index) =
        layout.patternWireMap (sourceContext.get index))
    (targetDisjoint : layout.plugRaw.WireEndpointsAreDisjoint)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (nodeRegion : (input.pattern.val.diagram.nodes node).region = sourceParent)
    (port : CPort) :
    resolvePort? layout.plugRaw targetContext
        (layout.patternNode node) port =
      (resolvePort? input.pattern.val.diagram sourceContext node port).map
        indexMap := by
  unfold resolvePort?
  rw [endpointOwner?_map node (layout.patternNode node)
    layout.patternWireMap port
    (fun wire occurs =>
      layout.endpointOccurs_patternNode_forward wire node port occurs)
    (fun targetWire occurs =>
      layout.endpointOccurs_patternNode_backward targetWire node port occurs)
    targetDisjoint]
  cases sourceOwner : endpointOwner? input.pattern.val.diagram
      ⟨node, port⟩ with
  | none => rfl
  | some sourceWire =>
      simp only [Option.map_some]
      have sourceOccurs : input.pattern.val.diagram.EndpointOccurs sourceWire
          ⟨node, port⟩ := endpointOwner?_sound sourceOwner
      have sourceEncloses :=
        input.pattern.property.diagram_well_formed.wire_scopes_enclose
          sourceWire ⟨node, port⟩ sourceOccurs
      have sourceMember : sourceWire ∈ sourceContext :=
        (sourceExact.mem_iff sourceWire).2 (by
          simpa only [nodeRegion] using sourceEncloses)
      obtain ⟨sourceIndex, sourceLookup⟩ :=
        WireContext.lookup?_complete sourceMember
      have sourceGet : sourceContext.get sourceIndex = sourceWire := by
        simpa only [List.get_eq_getElem] using
          WireContext.lookup?_sound sourceLookup
      have mappedGet : targetContext.get (indexMap sourceIndex) =
          layout.patternWireMap sourceWire :=
        (getMapped sourceIndex).trans
          (congrArg layout.patternWireMap sourceGet)
      have targetMember : layout.patternWireMap sourceWire ∈ targetContext := by
        rw [← mappedGet]
        exact List.get_mem _ _
      obtain ⟨targetIndex, targetLookup⟩ :=
        WireContext.lookup?_complete targetMember
      have targetGet : targetContext.get targetIndex =
          layout.patternWireMap sourceWire := by
        simpa only [List.get_eq_getElem] using
          WireContext.lookup?_sound targetLookup
      have indexEq : targetIndex = indexMap sourceIndex := by
        apply Fin.ext
        exact (List.getElem_inj targetNodup).mp (by
          simpa only [List.get_eq_getElem] using
            targetGet.trans mappedGet.symm)
      change targetContext.lookup? (layout.patternWireMap sourceWire) =
        (sourceContext.lookup? sourceWire).map indexMap
      rw [sourceLookup, targetLookup, indexEq]
      rfl

end Splice.Input.PlugLayout

end VisualProof.Concrete
