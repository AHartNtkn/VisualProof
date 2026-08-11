import VisualProof.Concrete.Elaboration.SpliceContext
import VisualProof.Concrete.Elaboration.SpliceWireLayout

/-! Source-derived wire and endpoint transport for pattern nodes in a splice. -/

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
noncomputable def patternWireMap (layout : PlugLayout input) :
    Fin input.pattern.val.diagram.wireCount → Fin layout.plugRaw.wireCount :=
  fun wire =>
    if exposed : wire ∈ input.pattern.val.exposedWires then
      layout.frameWire
        (layout.exposedAttachment (layout.exposedWireIndex wire exposed))
    else
      layout.internalWire (layout.internalWires.index wire (by
        rw [layout.internalWires_exact]
        exact decide_eq_true_iff.mpr exposed))

theorem patternWireMap_of_exposed (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (exposed : wire ∈ input.pattern.val.exposedWires) :
    layout.patternWireMap wire =
      layout.frameWire
        (layout.exposedAttachment (layout.exposedWireIndex wire exposed)) := by
  unfold patternWireMap
  rw [dif_pos exposed]

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

/-- The target full wire context used while compiling inserted pattern nodes:
the exact host-site context under the frame embedding, followed by the
terminal body's new internal locals. -/
noncomputable def patternSiteWires (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (hostContext : WireContext input.frame.val) : WireContext layout.plugRaw :=
  @List.append (Fin layout.plugRaw.wireCount)
    (hostContext.map (fun wire =>
      show Fin layout.plugRaw.wireCount from
        layout.frameWireEmbedding consistent wire))
    layout.bodyLocalWires

theorem bodyLocalWires_nodup (layout : PlugLayout input) :
    layout.bodyLocalWires.Nodup := by
  unfold bodyLocalWires
  refine (filterFin_nodup _).map layout.internalWire ?_
  intro left right distinct equality
  exact distinct (layout.internalWire_injective equality)

theorem patternSiteWires_nodup (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site) :
    (layout.patternSiteWires consistent hostContext).Nodup := by
  unfold patternSiteWires
  change ((hostContext.map (fun wire =>
      show Fin layout.plugRaw.wireCount from
        layout.frameWireEmbedding consistent wire)) ++
    layout.bodyLocalWires).Nodup
  rw [List.nodup_append]
  refine ⟨hostExact.nodup.map (fun wire =>
      (layout.frameWireEmbedding consistent wire :
        Fin layout.plugRaw.wireCount)) ?_,
    layout.bodyLocalWires_nodup, ?_⟩
  · intro left right distinct equality
    exact distinct (layout.frameWireEmbedding_injective consistent equality)
  · intro frame frameMember internal internalMember equality
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp frameMember
    unfold bodyLocalWires at internalMember
    obtain ⟨dense, _, rfl⟩ := List.mem_map.mp internalMember
    have values := congrArg Fin.val equality
    simp [frameWireEmbedding, frameWire, internalWire]
      at values
    omega

/-- Combined lexical index transport from the terminal pattern compiler's
inherited-and-local context to the raw plug's host-and-body context. -/
noncomputable def patternContextIndexMap (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent) (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site) :
    Fin (compiled.siteContext ++ compiled.siteLocals).length →
      Fin (layout.patternSiteWires consistent hostContext).length :=
  fun index =>
    Fin.cast (by simp [patternSiteWires])
      (Fin.addCases
        (fun inherited => Fin.castAdd layout.bodyLocalWires.length
          (compiled.spliceWireMap input layout admissible hostContext
            hostExact inherited))
        (fun localIndex => Fin.natAdd hostContext.length
          (layout.bodyLocalEquiv compiled localIndex))
        (Fin.cast (by simp) index))

private theorem patternWireMap_siteContext_get (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent) (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (index : Fin compiled.siteContext.length) :
    (hostContext.map (fun wire =>
      (layout.frameWireEmbedding consistent wire :
        Fin layout.plugRaw.wireCount))).get
        (Fin.cast (by simp)
          (compiled.spliceWireMap input layout admissible hostContext
            hostExact index)) =
      layout.patternWireMap (compiled.siteContext.get index) := by
  let external := compiled.spliceWireExternalIndex input index
  have sourceEq : compiled.siteContext.get index =
      input.pattern.val.exposedWires.get external := by
    exact (compiled.spliceWireMap_source_get input layout index).symm
      |>.trans (layout.boundary_get_exposedPosition external)
  calc
    _ = layout.frameWireEmbedding consistent
        (hostContext.get (compiled.spliceWireMap input layout admissible
          hostContext hostExact index)) := by
      simp only [List.get_eq_getElem, List.getElem_map]
      congr 2
    _ = layout.patternWireMap (compiled.siteContext.get index) := by
      have hostGet : hostContext.get
          (compiled.spliceWireMap input layout admissible hostContext
            hostExact index) =
          input.attachment (layout.exposedPosition external) := by
        simpa only [List.get_eq_getElem] using
          compiled.spliceWireMap_get input layout admissible
            hostContext hostExact index
      rw [hostGet, sourceEq,
        layout.patternWireMap_exposed_get external]
      rfl

private theorem patternWireMap_siteLocal_get (layout : PlugLayout input)
    (compiled : CompiledMaterial input)
    (index : Fin compiled.siteLocals.length) :
    layout.bodyLocalWires.get (layout.bodyLocalEquiv compiled index) =
      layout.patternWireMap (compiled.siteLocals.get index) := by
  obtain ⟨internal, sourceEq, targetEq⟩ :=
    layout.bodyLocalEquiv_get compiled index
  rw [sourceEq, targetEq, layout.patternWireMap_of_internal]

/-- The combined lexical index map names exactly the total transported source
wire at every inherited or local compiler position. -/
theorem patternContextIndexMap_get (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent) (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (index : Fin (compiled.siteContext ++ compiled.siteLocals).length) :
    (layout.patternSiteWires consistent hostContext).get
        (layout.patternContextIndexMap consistent admissible compiled
          hostContext hostExact index) =
      layout.patternWireMap
        ((compiled.siteContext ++ compiled.siteLocals).get index) := by
  let split : Fin
      (compiled.siteContext.length + compiled.siteLocals.length) :=
    Fin.cast (by simp) index
  have indexEq : Fin.cast (by simp) split = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · calc
      _ = (@List.append (Fin layout.plugRaw.wireCount)
            (hostContext.map (fun wire =>
              show Fin layout.plugRaw.wireCount from
                layout.frameWireEmbedding consistent wire))
            layout.bodyLocalWires).get
          (Fin.cast (by simp)
            (Fin.castAdd layout.bodyLocalWires.length
              (compiled.spliceWireMap input layout admissible hostContext
                hostExact inherited))) := by
          congr 1
          apply Fin.ext
          simp [patternContextIndexMap]
      _ = (hostContext.map (fun wire =>
              show Fin layout.plugRaw.wireCount from
                layout.frameWireEmbedding consistent wire)).get
          (Fin.cast (by simp)
            (compiled.spliceWireMap input layout admissible hostContext
              hostExact inherited)) :=
        by
          let mappedContext : WireContext layout.plugRaw :=
            hostContext.map (fun wire =>
              show Fin layout.plugRaw.wireCount from
                layout.frameWireEmbedding consistent wire)
          let mappedIndex : Fin mappedContext.length :=
            Fin.cast (by simp [mappedContext])
              (compiled.spliceWireMap input layout admissible hostContext
                hostExact inherited)
          change (mappedContext ++ layout.bodyLocalWires).get _ =
            mappedContext.get _
          calc
            _ = (mappedContext ++ layout.bodyLocalWires).get
                (Fin.cast (by simp)
                  (Fin.castAdd layout.bodyLocalWires.length mappedIndex)) := by
              congr 1
            _ = mappedContext.get mappedIndex :=
              get_append_castAdd mappedContext layout.bodyLocalWires mappedIndex
            _ = _ := by
              congr 1
      _ = layout.patternWireMap (compiled.siteContext.get inherited) :=
        layout.patternWireMap_siteContext_get consistent admissible compiled
          hostContext hostExact inherited
      _ = _ := by
        rw [get_append_castAdd]
  · calc
      _ = (@List.append (Fin layout.plugRaw.wireCount)
            (hostContext.map (fun wire =>
              show Fin layout.plugRaw.wireCount from
                layout.frameWireEmbedding consistent wire))
            layout.bodyLocalWires).get
          (Fin.cast (by simp)
            (Fin.natAdd hostContext.length
              (layout.bodyLocalEquiv compiled localIndex))) := by
          congr 1
          apply Fin.ext
          simp [patternContextIndexMap]
      _ = layout.bodyLocalWires.get
          (layout.bodyLocalEquiv compiled localIndex) := by
        let mappedContext : WireContext layout.plugRaw :=
          hostContext.map (fun wire =>
            show Fin layout.plugRaw.wireCount from
              layout.frameWireEmbedding consistent wire)
        change (mappedContext ++ layout.bodyLocalWires).get _ = _
        calc
          _ = (mappedContext ++ layout.bodyLocalWires).get
              (Fin.cast (by simp)
                (Fin.natAdd mappedContext.length
                  (layout.bodyLocalEquiv compiled localIndex))) := by
            congr 1
            apply Fin.ext
            simp [mappedContext]
          _ = _ := get_append_natAdd mappedContext layout.bodyLocalWires _
      _ = layout.patternWireMap (compiled.siteLocals.get localIndex) :=
        layout.patternWireMap_siteLocal_get compiled localIndex
      _ = _ := by
        rw [get_append_natAdd]

/-- Every endpoint owned by a source pattern wire is owned by its transported
wire at the corresponding pattern node in the raw plug. -/
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
    rw [← origin, layout.patternWireMap_of_internal]
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
      layout.patternWireMap_of_internal internal, ?_⟩
    simpa [endpointEq] using sourceOccurs

/-- Port resolution for a direct terminal-body pattern node commutes with the
source-derived splice context map.  This proof uses exact endpoint ownership
and lexical lookup directly, so distinct exposed classes may legitimately
share one attachment. -/
theorem resolvePort?_patternNode (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent) (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (targetDisjoint : layout.plugRaw.WireEndpointsAreDisjoint)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (nodeRegion : (input.pattern.val.diagram.nodes node).region =
      input.binderSpine.bodyContainer)
    (port : CPort) :
    resolvePort? layout.plugRaw
        (layout.patternSiteWires consistent hostContext)
        (layout.patternNode node) port =
      (resolvePort? input.pattern.val.diagram
        (compiled.siteContext ++ compiled.siteLocals) node port).map
        (layout.patternContextIndexMap consistent admissible compiled
          hostContext hostExact) := by
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
      have sourceEnclosesBody : input.pattern.val.diagram.Encloses
          (input.pattern.val.diagram.wires sourceWire).scope
          input.binderSpine.bodyContainer := by
        simpa only [nodeRegion] using sourceEncloses
      have sourceMember : sourceWire ∈
          compiled.siteContext ++ compiled.siteLocals :=
        (compiled.completeContext_exact.mem_iff sourceWire).2
          sourceEnclosesBody
      obtain ⟨sourceIndex, sourceLookup⟩ :=
        WireContext.lookup?_complete sourceMember
      have sourceGet :
          (compiled.siteContext ++ compiled.siteLocals).get sourceIndex =
            sourceWire := by
        simpa only [List.get_eq_getElem] using
          WireContext.lookup?_sound sourceLookup
      have mappedGet :
          (layout.patternSiteWires consistent hostContext).get
              (layout.patternContextIndexMap consistent admissible compiled
                hostContext hostExact sourceIndex) =
            layout.patternWireMap sourceWire :=
        (layout.patternContextIndexMap_get consistent admissible compiled
          hostContext hostExact sourceIndex).trans
            (congrArg layout.patternWireMap sourceGet)
      have targetMember : layout.patternWireMap sourceWire ∈
          layout.patternSiteWires consistent hostContext := by
        rw [← mappedGet]
        exact List.get_mem _ _
      obtain ⟨targetIndex, targetLookup⟩ :=
        WireContext.lookup?_complete targetMember
      have targetGet :
          (layout.patternSiteWires consistent hostContext).get targetIndex =
            layout.patternWireMap sourceWire := by
        simpa only [List.get_eq_getElem] using
          WireContext.lookup?_sound targetLookup
      have indexEq : targetIndex =
          layout.patternContextIndexMap consistent admissible compiled
            hostContext hostExact sourceIndex := by
        apply Fin.ext
        exact (List.getElem_inj
          (layout.patternSiteWires_nodup consistent hostContext hostExact)).mp
            (by
              simpa only [List.get_eq_getElem] using
                targetGet.trans mappedGet.symm)
      change (layout.patternSiteWires consistent hostContext).lookup?
          (layout.patternWireMap sourceWire) =
        ((compiled.siteContext ++ compiled.siteLocals).lookup?
          sourceWire).map
          (layout.patternContextIndexMap consistent admissible compiled
            hostContext hostExact)
      rw [sourceLookup, targetLookup, indexEq]
      rfl

end Splice.Input.PlugLayout

end VisualProof.Concrete
