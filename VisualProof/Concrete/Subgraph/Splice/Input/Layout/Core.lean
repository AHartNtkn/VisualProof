import VisualProof.Concrete.Subgraph.Splice.Input.Quotient

namespace VisualProof.Concrete.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace PlugLayout

def regionCount (layout : PlugLayout input) : Nat :=
  input.frame.val.regionCount + layout.materialRegions.count

@[simp] theorem materialRegions_count (layout : PlugLayout input) :
    layout.materialRegions.count =
      input.binderSpine.materialRegions.length := by
  simp only [SurvivorDomain.count_eq_filterFin_length]
  unfold BinderSpine.materialRegions
  congr 2
  funext region
  exact layout.materialRegions_exact region

def nodeCount (_layout : PlugLayout input) : Nat :=
  input.frame.val.nodeCount + input.pattern.val.diagram.nodeCount

def wireCount (layout : PlugLayout input) : Nat :=
  input.wireQuotient.count + layout.internalWires.count

def frameRegion (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) : Fin layout.regionCount :=
  Fin.castAdd layout.materialRegions.count region

def materialRegion (layout : PlugLayout input)
    (region : layout.materialRegions.Carrier) : Fin layout.regionCount :=
  Fin.natAdd input.frame.val.regionCount region

def frameNode (layout : PlugLayout input)
    (node : Fin input.frame.val.nodeCount) : Fin layout.nodeCount :=
  Fin.castAdd input.pattern.val.diagram.nodeCount node

def patternNode (layout : PlugLayout input)
    (node : Fin input.pattern.val.diagram.nodeCount) : Fin layout.nodeCount :=
  Fin.natAdd input.frame.val.nodeCount node

def frameWire (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) : Fin layout.wireCount :=
  Fin.castAdd layout.internalWires.count wire

def internalWire (layout : PlugLayout input)
    (wire : layout.internalWires.Carrier) : Fin layout.wireCount :=
  Fin.natAdd input.wireQuotient.count wire

def frameWireMap (layout : PlugLayout input)
    (wire : Fin input.frame.val.wireCount) : Fin layout.wireCount :=
  layout.frameWire (input.quotientWire wire)

def bodyRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Fin layout.regionCount :=
  match layout.materialRegions.index? region with
  | some material => layout.materialRegion material
  | none => layout.frameRegion input.site

def proxies (_layout : PlugLayout input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  (allFin input.binderSpine.proxyCount).map input.binderSpine.proxy

def proxyIndex? (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Option (Fin input.binderSpine.proxyCount) :=
  (indexOf? layout.proxies region).map (Fin.cast (by
    simp [proxies, allFin_eq_finRange]))

def binderRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Fin layout.regionCount :=
  match layout.proxyIndex? region with
  | some proxy => layout.frameRegion (input.binderTarget proxy)
  | none => layout.bodyRegion region

theorem frameWireMap_injective (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent) :
    Function.Injective layout.frameWireMap := by
  intro left right heq
  apply input.quotientWire_injective consistent
  unfold frameWireMap frameWire at heq
  apply Fin.ext
  simpa using congrArg Fin.val heq

@[simp] theorem bodyRegion_bodyContainer (layout : PlugLayout input) :
    layout.bodyRegion input.binderSpine.bodyContainer =
      layout.frameRegion input.site := by
  unfold bodyRegion
  have hdeleted : layout.materialRegions.survives
      input.binderSpine.bodyContainer = false := by
    rw [layout.materialRegions_exact]
    simp [input.binderSpine.bodyContainer_not_material]
  rw [(layout.materialRegions.index?_eq_none_iff _).2 hdeleted]

@[simp] theorem bodyRegion_material (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    layout.bodyRegion (layout.materialRegions.origin material) =
      layout.materialRegion material := by
  unfold bodyRegion
  rw [layout.materialRegions.index?_origin]

private theorem proxies_nodup (layout : PlugLayout input) :
    layout.proxies.Nodup := by
  apply (allFin_nodup _).map
  intro left right hne heq
  exact hne (input.binderSpine.proxy_injective heq)

@[simp] theorem proxyIndex?_proxy (layout : PlugLayout input)
    (proxy : Fin input.binderSpine.proxyCount) :
    layout.proxyIndex? (input.binderSpine.proxy proxy) = some proxy := by
  let lengthEq : layout.proxies.length = input.binderSpine.proxyCount := by
    simp [proxies, allFin_eq_finRange]
  let position : Fin layout.proxies.length := Fin.cast lengthEq.symm proxy
  have hget : layout.proxies.get position = input.binderSpine.proxy proxy := by
    simp [position, proxies, allFin_eq_finRange]
  have hindex := indexOf?_get_eq_some_of_nodup layout.proxies_nodup position
  unfold proxyIndex?
  rw [hget] at hindex
  rw [hindex]
  apply congrArg some
  apply Fin.ext
  rfl

@[simp] theorem binderRegion_proxy (layout : PlugLayout input)
    (proxy : Fin input.binderSpine.proxyCount) :
    layout.binderRegion (input.binderSpine.proxy proxy) =
      layout.frameRegion (input.binderTarget proxy) := by
  simp [binderRegion]

def mapPatternRegion (layout : PlugLayout input)
    (region : CRegion input.pattern.val.diagram.regionCount) :
    CRegion layout.regionCount :=
  match region with
  | .sheet => .cut (layout.frameRegion input.site)
  | .cut parent => .cut (layout.bodyRegion parent)
  | .bubble parent arity => .bubble (layout.bodyRegion parent) arity

def mapPatternNode (layout : PlugLayout input)
    (node : CNode input.pattern.val.diagram.regionCount) :
    CNode layout.regionCount :=
  match node with
  | .atom region binder =>
      .atom (layout.bodyRegion region) (layout.binderRegion binder)
  | .identity region arity =>
      .identity (layout.bodyRegion region) arity

def mapPatternEndpoint (layout : PlugLayout input)
    (endpoint : CEndpoint input.pattern.val.diagram.nodeCount) :
    CEndpoint layout.nodeCount :=
  { node := layout.patternNode endpoint.node, port := endpoint.port }

def mapFrameEndpoint (layout : PlugLayout input)
    (endpoint : CEndpoint input.frame.val.nodeCount) :
    CEndpoint layout.nodeCount :=
  { node := layout.frameNode endpoint.node, port := endpoint.port }

def mapPatternWire (layout : PlugLayout input)
    (wire : CWire input.pattern.val.diagram.regionCount
      input.pattern.val.diagram.nodeCount) :
    CWire layout.regionCount layout.nodeCount :=
  { scope := layout.bodyRegion wire.scope
    endpoints := wire.endpoints.map layout.mapPatternEndpoint }

def exposedPosition (_layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    Fin input.pattern.val.boundary.length :=
  (indexOf? input.pattern.val.boundary
    (input.pattern.val.exposedWires.get external)).get (by
      rw [indexOf?_isSome_iff]
      exact (OpenDiagram.mem_exposedWires _ _).1 (List.get_mem _ _))

def exposedAttachment (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    input.wireQuotient.Carrier :=
  input.quotientWire (input.attachment (layout.exposedPosition external))

def patternWireMap (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount) : Fin layout.wireCount :=
  if exposed : wire ∈ input.pattern.val.exposedWires then
    let position := (indexOf? input.pattern.val.exposedWires wire).get
      ((indexOf?_isSome_iff).2 exposed)
    layout.frameWire (layout.exposedAttachment position)
  else
    layout.internalWire (layout.internalWires.index wire (by
      rw [layout.internalWires_exact]
      simp [exposed]))

@[simp] theorem patternWireMap_exposed (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    layout.patternWireMap (input.pattern.val.exposedWires.get external) =
      layout.frameWire (layout.exposedAttachment external) := by
  unfold patternWireMap
  split
  next exposed =>
    have hindex := indexOf?_get_eq_some_of_nodup
      input.pattern.val.exposedWires_nodup external
    have hsome : (indexOf? input.pattern.val.exposedWires
        (input.pattern.val.exposedWires.get external)).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨external, hindex⟩
    rw [Option.get_of_eq_some hsome hindex]
  next notExposed =>
    exact False.elim (notExposed (List.get_mem _ _))

@[simp] theorem patternWireMap_internal (layout : PlugLayout input)
    (internal : layout.internalWires.Carrier) :
    layout.patternWireMap (layout.internalWires.origin internal) =
      layout.internalWire internal := by
  unfold patternWireMap
  split
  next exposed =>
    have survives := layout.internalWires.origin_survives internal
    rw [layout.internalWires_exact] at survives
    exact False.elim ((of_decide_eq_true survives) exposed)
  next notExposed =>
    exact congrArg layout.internalWire
      (layout.internalWires.index_origin internal)

def boundaryWires (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    List (Fin input.pattern.val.diagram.wireCount) :=
  ((allFin input.pattern.val.exposedWires.length).filter fun external =>
    decide (layout.exposedAttachment external = quotient)).map fun external =>
      input.pattern.val.exposedWires.get external

def boundaryEndpoints (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    List (CEndpoint layout.nodeCount) :=
  ((layout.boundaryWires quotient).flatMap fun wire =>
    (input.pattern.val.diagram.wires wire).endpoints).map
      layout.mapPatternEndpoint

def mapFrameRegion (layout : PlugLayout input) :
    CRegion input.frame.val.regionCount → CRegion layout.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (layout.frameRegion parent)
  | .bubble parent arity => .bubble (layout.frameRegion parent) arity

def mapFrameNode (layout : PlugLayout input) :
    CNode input.frame.val.regionCount → CNode layout.regionCount
  | .atom region binder =>
      .atom (layout.frameRegion region) (layout.frameRegion binder)
  | .identity region arity =>
      .identity (layout.frameRegion region) arity

def plugRegion (layout : PlugLayout input)
    (region : Fin layout.regionCount) : CRegion layout.regionCount :=
  Fin.addCases
    (fun frameRegion => layout.mapFrameRegion
      (input.frame.val.regions frameRegion))
    (fun material => layout.mapPatternRegion
      (input.pattern.val.diagram.regions
        (layout.materialRegions.origin material))) region

def plugNode (layout : PlugLayout input)
    (node : Fin layout.nodeCount) : CNode layout.regionCount :=
  Fin.addCases
    (fun frameNode => layout.mapFrameNode (input.frame.val.nodes frameNode))
    (fun patternNode => layout.mapPatternNode
      (input.pattern.val.diagram.nodes patternNode)) node

def plugWire (layout : PlugLayout input)
    (wire : Fin layout.wireCount) : CWire layout.regionCount layout.nodeCount :=
  Fin.addCases
    (fun quotient => {
      scope := layout.frameRegion (input.coalescedScope quotient)
      endpoints :=
        (input.coalescedEndpoints quotient).map layout.mapFrameEndpoint ++
          layout.boundaryEndpoints quotient
    })
    (fun internal => layout.mapPatternWire
      (input.pattern.val.diagram.wires
        (layout.internalWires.origin internal))) wire

def plugRaw (layout : PlugLayout input) : Diagram where
  regionCount := layout.regionCount
  nodeCount := layout.nodeCount
  wireCount := layout.wireCount
  root := layout.frameRegion input.frame.val.root
  regions := layout.plugRegion
  nodes := layout.plugNode
  wires := layout.plugWire

@[simp] theorem plugRaw_regions_frame (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    layout.plugRaw.regions (layout.frameRegion region) =
      layout.mapFrameRegion (input.frame.val.regions region) := by
  simp [plugRaw, plugRegion, frameRegion]

@[simp] theorem plugRaw_regions_material (layout : PlugLayout input)
    (region : layout.materialRegions.Carrier) :
    layout.plugRaw.regions (layout.materialRegion region) =
      layout.mapPatternRegion
        (input.pattern.val.diagram.regions
          (layout.materialRegions.origin region)) := by
  simp [plugRaw, plugRegion, materialRegion]

@[simp] theorem plugRaw_nodes_frame (layout : PlugLayout input)
    (node : Fin input.frame.val.nodeCount) :
    layout.plugRaw.nodes (layout.frameNode node) =
      layout.mapFrameNode (input.frame.val.nodes node) := by
  simp [plugRaw, plugNode, frameNode]

@[simp] theorem plugRaw_nodes_pattern (layout : PlugLayout input)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    layout.plugRaw.nodes (layout.patternNode node) =
      layout.mapPatternNode (input.pattern.val.diagram.nodes node) := by
  simp [plugRaw, plugNode, patternNode]

@[simp] theorem plugRaw_wires_frame (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) :
    layout.plugRaw.wires (layout.frameWire wire) = {
      scope := layout.frameRegion (input.coalescedScope wire)
      endpoints :=
        (input.coalescedEndpoints wire).map layout.mapFrameEndpoint ++
          layout.boundaryEndpoints wire
    } := by
  simp [plugRaw, plugWire, frameWire]

@[simp] theorem plugRaw_wires_internal (layout : PlugLayout input)
    (wire : layout.internalWires.Carrier) :
    layout.plugRaw.wires (layout.internalWire wire) =
      layout.mapPatternWire
        (input.pattern.val.diagram.wires
          (layout.internalWires.origin wire)) := by
  simp [plugRaw, plugWire, internalWire]

def outputOpenRoot (input : Input) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) : OpenDiagram where
  diagram := layout.plugRaw
  boundary := sourceBoundary.map (layout.frameWire ∘ input.quotientWire)

end PlugLayout

end VisualProof.Concrete.Splice.Input
