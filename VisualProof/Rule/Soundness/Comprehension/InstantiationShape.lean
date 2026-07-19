import VisualProof.Rule.Soundness.Comprehension.InstantiationMaps

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

def mapRegionShape (map : Fin source → Fin target) :
    CRegion source → CRegion target
  | .sheet => .sheet
  | .cut parent => .cut (map parent)
  | .bubble parent arity => .bubble (map parent) arity

def mapNodeShape (map : Fin source → Fin target) :
    CNode source → CNode target
  | .term region freePorts term => .term (map region) freePorts term
  | .atom region binder => .atom (map region) (map binder)
  | .named region definition arity => .named (map region) definition arity

@[simp] theorem mapRegionShape_comp
    (first : Fin source → Fin middle)
    (second : Fin middle → Fin target)
    (region : CRegion source) :
    mapRegionShape second (mapRegionShape first region) =
      mapRegionShape (second ∘ first) region := by
  cases region <;> rfl

@[simp] theorem mapNodeShape_comp
    (first : Fin source → Fin middle)
    (second : Fin middle → Fin target)
    (node : CNode source) :
    mapNodeShape second (mapNodeShape first node) =
      mapNodeShape (second ∘ first) node := by
  cases node <;> rfl

theorem region_shape
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (region : Fin state.diagram.val.regionCount) :
    result.diagram.val.regions (trace.regionMap region) =
      mapRegionShape trace.regionMap (state.diagram.val.regions region) := by
  induction trace with
  | done fuel current pending_empty =>
      cases hregion : current.diagram.val.regions region <;>
        simp [regionMap, mapRegionShape, hregion]
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let spliceInput := instantiateSpliceInput comprehension attachments
        binders payload state site arguments
      let layout := spliceInput.plugLayout
      rw [show (InstantiationTrace.step fuel state result atom tail site
        candidate arguments checkedInput pending_eq node_eq candidate_eq
        arguments_eq input_eq rest).regionMap region =
          rest.regionMap (layout.frameRegion region) from rfl]
      rw [ih (layout.frameRegion region)]
      change mapRegionShape rest.regionMap
          (layout.plugRegion (layout.frameRegion region)) = _
      rw [layout.plugRegion_frameRegion]
      cases hregion : state.diagram.val.regions region <;>
        simp [hregion, Splice.Input.PlugLayout.mapFrameRegion,
          mapRegionShape, regionMap, instantiateSpliceInput, spliceInput,
          layout]

theorem node_shape
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (node : Fin state.diagram.val.nodeCount) :
    result.diagram.val.nodes (trace.nodeMap node) =
      mapNodeShape trace.regionMap (state.diagram.val.nodes node) := by
  induction trace with
  | done fuel current pending_empty =>
      cases hnode : current.diagram.val.nodes node <;>
        simp [nodeMap, regionMap, mapNodeShape, hnode]
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let spliceInput := instantiateSpliceInput comprehension attachments
        binders payload state site arguments
      let layout := spliceInput.plugLayout
      rw [show (InstantiationTrace.step fuel state result atom tail site
        candidate arguments checkedInput pending_eq node_eq candidate_eq
        arguments_eq input_eq rest).nodeMap node =
          rest.nodeMap (layout.frameNode node) from rfl]
      rw [ih (layout.frameNode node)]
      change mapNodeShape rest.regionMap
          (layout.plugNode (layout.frameNode node)) = _
      rw [layout.plugNode_frameNode]
      cases hnode : state.diagram.val.nodes node <;>
        simp [hnode, Splice.Input.PlugLayout.mapFrameNode, mapNodeShape,
          regionMap, instantiateSpliceInput, spliceInput, layout]

end InstantiationTrace

end VisualProof.Rule
