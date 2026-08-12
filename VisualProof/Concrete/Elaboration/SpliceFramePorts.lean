import VisualProof.Concrete.Elaboration.SpliceWireLayout
import VisualProof.Concrete.Elaboration.Compile.Kernel

/-! Port-resolution transport for retained frame nodes in a source-derived splice. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

/-- Every endpoint occurrence of a retained frame node survives on the
embedded frame wire. -/
theorem endpointOccurs_frameNode_forward
    (layout : PlugLayout input)
    (wire : Fin input.frame.val.wireCount)
    (node : Fin input.frame.val.nodeCount) (port : CPort)
    (occurs : input.frame.val.EndpointOccurs wire ⟨node, port⟩) :
    layout.plugRaw.EndpointOccurs
      (layout.frameWireMap wire)
      ⟨layout.frameNode node, port⟩ := by
  change ⟨layout.frameNode node, port⟩ ∈
    (layout.plugRaw.wires
      (layout.frameWireMap wire)).endpoints
  simp only [frameWireMap, PlugLayout.plugRaw,
    PlugLayout.plugWire, PlugLayout.frameWire, Fin.addCases_left]
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨⟨node, port⟩, input.endpointOccurs_quotient wire _ occurs, rfl⟩

private theorem mapFrameEndpoint_injective (layout : PlugLayout input) :
    Function.Injective layout.mapFrameEndpoint := by
  intro left right equality
  cases left with
  | mk leftNode leftPort =>
      cases right with
      | mk rightNode rightPort =>
          simp only [PlugLayout.mapFrameEndpoint, PlugLayout.frameNode,
            CEndpoint.mk.injEq] at equality
          have nodeValues := congrArg Fin.val equality.1
          have nodeEquality : leftNode = rightNode := by
            apply Fin.ext
            simpa only [Fin.val_castAdd] using nodeValues
          cases nodeEquality
          cases equality.2
          rfl

private theorem mapPatternEndpoint_ne_frameNode
    (layout : PlugLayout input)
    (endpoint : CEndpoint input.pattern.val.diagram.nodeCount)
    (node : Fin input.frame.val.nodeCount) (port : CPort) :
    layout.mapPatternEndpoint endpoint ≠ ⟨layout.frameNode node, port⟩ := by
  intro equality
  have nodeEquality := congrArg CEndpoint.node equality
  have values := congrArg Fin.val nodeEquality
  simp only [PlugLayout.mapPatternEndpoint, PlugLayout.patternNode,
    PlugLayout.frameNode, Fin.val_natAdd, Fin.val_castAdd] at values
  omega

/-- Every target wire owning a retained frame-node endpoint is the image of
a source frame wire owning the corresponding source endpoint. -/
theorem endpointOccurs_frameNode_backward
    (layout : PlugLayout input)
    (targetWire : Fin layout.wireCount)
    (node : Fin input.frame.val.nodeCount) (port : CPort)
    (occurs : layout.plugRaw.EndpointOccurs targetWire
      ⟨layout.frameNode node, port⟩) :
    ∃ sourceWire : Fin input.frame.val.wireCount,
      layout.frameWireMap sourceWire = targetWire ∧
        input.frame.val.EndpointOccurs sourceWire ⟨node, port⟩ := by
  refine Fin.addCases (motive := fun targetWire =>
    layout.plugRaw.EndpointOccurs targetWire
        ⟨layout.frameNode node, port⟩ →
      ∃ sourceWire : Fin input.frame.val.wireCount,
        layout.frameWireMap sourceWire = targetWire ∧
          input.frame.val.EndpointOccurs sourceWire ⟨node, port⟩)
    ?_ ?_ targetWire occurs
  · intro quotient targetOccurs
    simp only [Diagram.EndpointOccurs, PlugLayout.plugRaw,
      PlugLayout.plugWire, Fin.addCases_left] at targetOccurs
    rcases List.mem_append.mp targetOccurs with frameOccurs | boundaryOccurs
    · obtain ⟨sourceEndpoint, sourceEndpointOccurs, endpointEquality⟩ :=
        List.mem_map.mp frameOccurs
      have sourceEndpointEq : sourceEndpoint = ⟨node, port⟩ :=
        layout.mapFrameEndpoint_injective endpointEquality
      subst sourceEndpoint
      rw [input.mem_coalescedEndpoints] at sourceEndpointOccurs
      obtain ⟨sourceWire, sourceClass, sourceOccurs⟩ := sourceEndpointOccurs
      refine ⟨sourceWire, ?_, sourceOccurs⟩
      exact congrArg layout.frameWire
        ((input.mem_classWires quotient sourceWire).1 sourceClass)
    · unfold PlugLayout.boundaryEndpoints at boundaryOccurs
      obtain ⟨patternEndpoint, _, endpointEquality⟩ :=
        List.mem_map.mp boundaryOccurs
      exact (layout.mapPatternEndpoint_ne_frameNode patternEndpoint node port
        endpointEquality).elim
  · intro internal targetOccurs
    simp only [Diagram.EndpointOccurs, PlugLayout.plugRaw,
      PlugLayout.plugWire, Fin.addCases_right] at targetOccurs
    unfold PlugLayout.mapPatternWire at targetOccurs
    obtain ⟨patternEndpoint, _, endpointEquality⟩ :=
      List.mem_map.mp targetOccurs
    exact (layout.mapPatternEndpoint_ne_frameNode patternEndpoint node port
      endpointEquality).elim

/-- Exact retained ownership on a fixed embedded frame wire. -/
theorem endpointOccurs_frameWireEmbedding_frameNode_iff
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount)
    (node : Fin input.frame.val.nodeCount) (port : CPort) :
    layout.plugRaw.EndpointOccurs
        (layout.frameWireMap wire)
        ⟨layout.frameNode node, port⟩ ↔
      input.frame.val.EndpointOccurs wire ⟨node, port⟩ := by
  constructor
  · intro targetOccurs
    obtain ⟨sourceWire, mapped, sourceOccurs⟩ :=
      layout.endpointOccurs_frameNode_backward
        (layout.frameWireMap wire) node port targetOccurs
    have sourceEq : sourceWire = wire :=
      layout.frameWireMap_injective consistent mapped
    simpa [sourceEq] using sourceOccurs
  · exact layout.endpointOccurs_frameNode_forward wire node port

/-- Resolve one retained frame-node port in any target lexical context that
contains the embedded source positions and reflects visibility for that port. -/
theorem resolvePort?_frameNode_map
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (sourceNode : Fin input.frame.val.nodeCount)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (targetNodup : targetContext.Nodup)
    (getMapped : ∀ index,
      targetContext.get (indexMap index) =
        layout.frameWireMap (sourceContext.get index))
    (visibleReflection : ∀ wire port,
      input.frame.val.EndpointOccurs wire ⟨sourceNode, port⟩ →
        layout.frameWireMap wire ∈ targetContext →
          wire ∈ sourceContext)
    (targetDisjoint : layout.plugRaw.WireEndpointsAreDisjoint)
    (port : CPort) :
    resolvePort? layout.plugRaw targetContext
        (layout.frameNode sourceNode) port =
      (resolvePort? input.frame.val sourceContext sourceNode port).map
        indexMap := by
  exact resolvePort?_map_of_embedding sourceContext targetContext sourceNode
    (layout.frameNode sourceNode) (layout.frameWireMap)
    (layout.frameWireMap_injective consistent) indexMap targetNodup
    getMapped
    (fun wire sourceOccurs =>
      layout.endpointOccurs_frameNode_forward wire sourceNode port
        sourceOccurs)
    (fun targetWire targetOccurs =>
      layout.endpointOccurs_frameNode_backward targetWire
        sourceNode port targetOccurs)
    (fun wire sourceOccurs targetMember =>
      visibleReflection wire port sourceOccurs targetMember)
    targetDisjoint

end Splice.Input.PlugLayout

end VisualProof.Concrete
