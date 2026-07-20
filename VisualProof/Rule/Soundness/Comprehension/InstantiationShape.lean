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

private theorem regionShape_transport
    {signature : List Nat}
    {source target : CheckedDiagram signature}
    (h : source = target)
    (region : Fin target.val.regionCount) :
    source.val.regions
        (Fin.cast (congrArg (fun diagram => diagram.val.regionCount) h.symm)
          region) =
      mapRegionShape
        (Fin.cast (congrArg (fun diagram => diagram.val.regionCount) h.symm))
        (target.val.regions region) := by
  cases h
  simp only [Fin.cast_refl, id_eq]
  cases source.val.regions region <;> rfl

private theorem nodeShape_transport
    {signature : List Nat}
    {source target : CheckedDiagram signature}
    (h : source = target)
    (node : Fin target.val.nodeCount) :
    source.val.nodes
        (Fin.cast (congrArg (fun diagram => diagram.val.nodeCount) h.symm)
          node) =
      mapNodeShape
        (Fin.cast (congrArg (fun diagram => diagram.val.regionCount) h.symm))
        (target.val.nodes node) := by
  cases h
  simp only [Fin.cast_refl, id_eq]
  cases source.val.nodes node <;> rfl

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
  | step fuel state result atom tail site candidate arguments plan pending_eq
      node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      let pluggedDiagram : CheckedDiagram signature :=
        ⟨layout.plugRaw,
          Splice.Input.PlugLayout.plugRaw_wellFormed signature spliceInput layout
            (Splice.Input.checkInput_sound plan.checkedInputChecked).2⟩
      have nextDiagramEq : plan.next.diagram = pluggedDiagram := by
        rw [plan.next_eq]
        rfl
      let regionCountEq : layout.regionCount = plan.next.diagram.val.regionCount :=
        congrArg (fun diagram => diagram.val.regionCount) nextDiagramEq.symm
      have nextRegions (source : Fin layout.regionCount) :
          plan.next.diagram.val.regions (Fin.cast regionCountEq source) =
            mapRegionShape (Fin.cast regionCountEq)
              (layout.plugRegion source) := by
        exact regionShape_transport nextDiagramEq source
      let mapped := Fin.cast regionCountEq (layout.frameRegion region)
      rw [show (InstantiationTrace.step fuel state result atom tail site
        candidate arguments plan pending_eq node_eq candidate_eq arguments_eq
        rest).regionMap region = rest.regionMap mapped from rfl]
      rw [ih mapped]
      have mappedShape := nextRegions (layout.frameRegion region)
      rw [mappedShape]
      rw [layout.plugRegion_frameRegion]
      cases hregion : state.diagram.val.regions region <;>
        simp [hregion, Splice.Input.PlugLayout.mapFrameRegion, mapRegionShape,
          regionMap, InstantiationCopyPlan.spliceInput,
          materializedInstantiationSpliceInput, instantiateSpliceInput,
          spliceInput, layout]

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
  | step fuel state result atom tail site candidate arguments plan pending_eq
      node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      let pluggedDiagram : CheckedDiagram signature :=
        ⟨layout.plugRaw,
          Splice.Input.PlugLayout.plugRaw_wellFormed signature spliceInput layout
            (Splice.Input.checkInput_sound plan.checkedInputChecked).2⟩
      have nextDiagramEq : plan.next.diagram = pluggedDiagram := by
        rw [plan.next_eq]
        rfl
      let regionCountEq : layout.regionCount = plan.next.diagram.val.regionCount :=
        congrArg (fun diagram => diagram.val.regionCount) nextDiagramEq.symm
      let nodeCountEq : layout.nodeCount = plan.next.diagram.val.nodeCount :=
        congrArg (fun diagram => diagram.val.nodeCount) nextDiagramEq.symm
      have nextNodes (source : Fin layout.nodeCount) :
          plan.next.diagram.val.nodes (Fin.cast nodeCountEq source) =
            mapNodeShape (Fin.cast regionCountEq) (layout.plugNode source) := by
        exact nodeShape_transport nextDiagramEq source
      let mapped := Fin.cast nodeCountEq (layout.frameNode node)
      rw [show (InstantiationTrace.step fuel state result atom tail site
        candidate arguments plan pending_eq node_eq candidate_eq arguments_eq
        rest).nodeMap node = rest.nodeMap mapped from rfl]
      rw [ih mapped]
      have mappedShape := nextNodes (layout.frameNode node)
      rw [mappedShape]
      rw [layout.plugNode_frameNode]
      cases hnode : state.diagram.val.nodes node <;>
        simp [hnode, Splice.Input.PlugLayout.mapFrameNode, mapNodeShape,
          regionMap, InstantiationCopyPlan.spliceInput,
          materializedInstantiationSpliceInput, instantiateSpliceInput,
          spliceInput, layout]

end InstantiationTrace

end VisualProof.Rule
