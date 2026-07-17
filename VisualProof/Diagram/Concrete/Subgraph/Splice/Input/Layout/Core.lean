import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Quotient

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace PlugLayout

@[simp] theorem materialRegions_survives_iff (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    layout.materialRegions.survives region = true ↔
      input.binderSpine.IsMaterialRegion region := by
  rw [layout.materialRegions_exact]
  exact decide_eq_true_iff

@[simp] theorem internalWires_survives_iff (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    layout.internalWires.survives wire = true ↔
      wire ∉ input.pattern.val.exposedWires := by
  rw [layout.internalWires_exact]
  exact decide_eq_true_iff

def regionCount (layout : PlugLayout input) : Nat :=
  input.frame.val.regionCount + layout.materialRegions.count

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

def quotientBlockWire (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) : Fin layout.wireCount :=
  Fin.castAdd layout.internalWires.count wire

def internalBlockWire (layout : PlugLayout input)
    (wire : layout.internalWires.Carrier) : Fin layout.wireCount :=
  Fin.natAdd input.wireQuotient.count wire

def frameWire (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) : Fin layout.wireCount :=
  Fin.castAdd layout.internalWires.count wire

def internalWire (layout : PlugLayout input)
    (wire : layout.internalWires.Carrier) : Fin layout.wireCount :=
  Fin.natAdd input.wireQuotient.count wire

def bodyRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Fin layout.regionCount :=
  match layout.materialRegions.index? region with
  | some material => layout.materialRegion material
  | none => layout.frameRegion input.site

theorem frameRegion_injective (layout : PlugLayout input) :
    Function.Injective layout.frameRegion := by
  intro left right heq
  apply Fin.ext
  exact congrArg (fun index => index.val) heq

@[simp] theorem frameRegion_eq_iff (layout : PlugLayout input)
    (left right : Fin input.frame.val.regionCount) :
    layout.frameRegion left = layout.frameRegion right ↔ left = right :=
  ⟨fun heq => layout.frameRegion_injective heq, congrArg layout.frameRegion⟩

theorem frameWire_injective (layout : PlugLayout input) :
    Function.Injective layout.frameWire := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg (fun value => value.val) heq
  simpa [frameWire] using hvals

theorem internalWire_injective (layout : PlugLayout input) :
    Function.Injective layout.internalWire := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg Fin.val heq
  simp [internalWire] at hvals
  omega

theorem frameWire_ne_internalWire (layout : PlugLayout input)
    (frame : input.wireQuotient.Carrier)
    (internal : layout.internalWires.Carrier) :
    layout.frameWire frame ≠ layout.internalWire internal := by
  intro heq
  have hvals := congrArg Fin.val heq
  simp [frameWire, internalWire] at hvals
  omega

theorem materialRegion_injective (layout : PlugLayout input) :
    Function.Injective layout.materialRegion := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg Fin.val heq
  simp [materialRegion] at hvals
  omega

theorem frameRegion_ne_materialRegion (layout : PlugLayout input)
    (frame : Fin input.frame.val.regionCount)
    (material : layout.materialRegions.Carrier) :
    layout.frameRegion frame ≠ layout.materialRegion material := by
  intro heq
  have hvals := congrArg Fin.val heq
  simp [frameRegion, materialRegion] at hvals
  omega

def materialIndex (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    layout.materialRegions.Carrier :=
  layout.materialRegions.index region
    ((layout.materialRegions_survives_iff region).2 hmaterial)

@[simp] theorem bodyRegion_material (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    layout.bodyRegion region = layout.materialRegion
      (layout.materialIndex region hmaterial) := by
  unfold bodyRegion materialIndex
  rw [layout.materialRegions.index?_index]

@[simp] theorem bodyRegion_origin (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    layout.bodyRegion (layout.materialRegions.origin material) =
      layout.materialRegion material := by
  have hmaterial : input.binderSpine.IsMaterialRegion
      (layout.materialRegions.origin material) :=
    (layout.materialRegions_survives_iff _).1
      (layout.materialRegions.origin_survives material)
  rw [layout.bodyRegion_material _ hmaterial]
  apply congrArg layout.materialRegion
  apply layout.materialRegions.origin_injective
  simp only [materialIndex, layout.materialRegions.origin_index]

theorem bodyRegion_nonmaterial (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : ¬ input.binderSpine.IsMaterialRegion region) :
    layout.bodyRegion region = layout.frameRegion input.site := by
  unfold bodyRegion
  have hfalse : layout.materialRegions.survives region = false := by
    rw [layout.materialRegions_exact]
    simp [hmaterial]
  rw [(layout.materialRegions.index?_eq_none_iff region).2 hfalse]

@[simp] theorem bodyRegion_root (layout : PlugLayout input) :
    layout.bodyRegion input.pattern.val.diagram.root =
      layout.frameRegion input.site := by
  apply layout.bodyRegion_nonmaterial
  simp [BinderSpine.IsMaterialRegion]

@[simp] theorem bodyRegion_proxy (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) :
    layout.bodyRegion (input.binderSpine.proxy index) =
      layout.frameRegion input.site := by
  apply layout.bodyRegion_nonmaterial
  intro hmaterial
  exact hmaterial.2 index rfl

@[simp] theorem bodyRegion_bodyContainer (layout : PlugLayout input) :
    layout.bodyRegion input.binderSpine.bodyContainer =
      layout.frameRegion input.site := by
  by_cases hzero : input.binderSpine.proxyCount = 0
  · rw [input.binderSpine.body_eq_root_of_empty hzero,
      layout.bodyRegion_root]
  · rw [input.binderSpine.body_eq_terminal_of_nonempty hzero,
      layout.bodyRegion_proxy]

theorem frameNode_injective (layout : PlugLayout input) :
    Function.Injective layout.frameNode := by
  intro left right heq
  apply Fin.ext
  exact congrArg (fun index => index.val) heq

theorem patternNode_injective (layout : PlugLayout input) :
    Function.Injective layout.patternNode := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg Fin.val heq
  simp [patternNode] at hvals
  omega

theorem frameNode_ne_patternNode (layout : PlugLayout input)
    (frame : Fin input.frame.val.nodeCount)
    (pattern : Fin input.pattern.val.diagram.nodeCount) :
    layout.frameNode frame ≠ layout.patternNode pattern := by
  intro heq
  have hvals := congrArg Fin.val heq
  simp [frameNode, patternNode] at hvals
  omega

def proxies (_layout : PlugLayout input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  (allFin input.binderSpine.proxyCount).map input.binderSpine.proxy

theorem proxies_nodup (layout : PlugLayout input) : layout.proxies.Nodup :=
  List.Pairwise.map (R := fun left right => left ≠ right)
    (S := fun left right => left ≠ right) input.binderSpine.proxy (by
      intro left right hne heq
      exact hne (input.binderSpine.proxy_injective heq))
    (allFin_nodup _)

def proxyIndex? (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Option (Fin input.binderSpine.proxyCount) :=
  (indexOf? layout.proxies region).map (Fin.cast (by
    simp [proxies, allFin_eq_finRange]))

def proxyPosition (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) : Fin layout.proxies.length :=
  Fin.cast (by simp [proxies, allFin_eq_finRange]) index

@[simp] theorem proxies_get_proxyPosition (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) :
    layout.proxies.get (layout.proxyPosition index) =
      input.binderSpine.proxy index := by
  simp [proxies, proxyPosition, allFin_eq_finRange]

@[simp] theorem proxyIndex?_proxy (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) :
    layout.proxyIndex? (input.binderSpine.proxy index) = some index := by
  unfold proxyIndex?
  have hlookup : indexOf? layout.proxies
      (input.binderSpine.proxy index) = some (layout.proxyPosition index) := by
    rw [← layout.proxies_get_proxyPosition index]
    exact indexOf?_get_eq_some_of_nodup layout.proxies_nodup _
  rw [hlookup]
  apply congrArg some
  apply Fin.ext
  rfl

theorem proxyIndex?_eq_none_of_material (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    layout.proxyIndex? region = none := by
  unfold proxyIndex?
  cases hlookup : indexOf? layout.proxies region with
  | none => rfl
  | some found =>
      have hsound := indexOf?_sound hlookup
      have hmember : region ∈ layout.proxies := by
        rw [← hsound]
        exact List.get_mem _ _
      rw [proxies, List.mem_map] at hmember
      rcases hmember with ⟨index, _, hproxy⟩
      exact False.elim (hmaterial.2 index hproxy.symm)

def binderRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Fin layout.regionCount :=
  match layout.proxyIndex? region with
  | some proxy => layout.frameRegion (input.binderTarget proxy)
  | none => layout.bodyRegion region

@[simp] theorem binderRegion_proxy (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) :
    layout.binderRegion (input.binderSpine.proxy index) =
      layout.frameRegion (input.binderTarget index) := by
  simp [binderRegion]

@[simp] theorem binderRegion_material (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    layout.binderRegion region = layout.bodyRegion region := by
  unfold binderRegion
  rw [layout.proxyIndex?_eq_none_of_material region hmaterial]

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
  | .term region freePorts term =>
      .term (layout.bodyRegion region) freePorts term
  | .atom region binder =>
      .atom (layout.bodyRegion region) (layout.binderRegion binder)
  | .named region definition arity =>
      .named (layout.bodyRegion region) definition arity

def mapPatternEndpoint (layout : PlugLayout input)
    (endpoint : CEndpoint input.pattern.val.diagram.nodeCount) :
    CEndpoint layout.nodeCount :=
  { node := layout.patternNode endpoint.node, port := endpoint.port }

def mapFrameEndpoint (layout : PlugLayout input)
    (endpoint : CEndpoint input.frame.val.nodeCount) :
    CEndpoint layout.nodeCount :=
  { node := layout.frameNode endpoint.node, port := endpoint.port }

theorem mapFrameEndpoint_injective (layout : PlugLayout input) :
    Function.Injective layout.mapFrameEndpoint := by
  intro left right heq
  cases left with
  | mk leftNode leftPort =>
    cases right with
    | mk rightNode rightPort =>
      simp only [mapFrameEndpoint] at heq
      have hnodes : leftNode = rightNode :=
        layout.frameNode_injective (congrArg CEndpoint.node heq)
      have hports : leftPort = rightPort := congrArg CEndpoint.port heq
      subst rightNode
      subst rightPort
      rfl

theorem mapFrameEndpoint_ne_mapPatternEndpoint (layout : PlugLayout input)
    (frame : CEndpoint input.frame.val.nodeCount)
    (pattern : CEndpoint input.pattern.val.diagram.nodeCount) :
    layout.mapFrameEndpoint frame ≠ layout.mapPatternEndpoint pattern := by
  intro heq
  exact layout.frameNode_ne_patternNode frame.node pattern.node
    (congrArg CEndpoint.node heq)

theorem mapPatternEndpoint_injective (layout : PlugLayout input) :
    Function.Injective layout.mapPatternEndpoint := by
  intro left right heq
  cases left with
  | mk leftNode leftPort =>
    cases right with
    | mk rightNode rightPort =>
      simp only [mapPatternEndpoint] at heq
      have hnodes : leftNode = rightNode :=
        layout.patternNode_injective (congrArg CEndpoint.node heq)
      have hports : leftPort = rightPort := congrArg CEndpoint.port heq
      subst rightNode
      subst rightPort
      rfl

def mapPatternWire (layout : PlugLayout input)
    (wire : CWire input.pattern.val.diagram.regionCount
      input.pattern.val.diagram.nodeCount) :
    CWire layout.regionCount layout.nodeCount :=
  { scope := layout.bodyRegion wire.scope
    endpoints := wire.endpoints.map layout.mapPatternEndpoint }

/-- First ordered boundary position carrying one exposed wire identity. -/
def exposedPosition (_layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    Fin input.pattern.val.boundary.length :=
  (indexOf? input.pattern.val.boundary
    (input.pattern.val.exposedWires.get external)).get (by
      rw [indexOf?_isSome_iff]
      exact (OpenConcreteDiagram.mem_exposedWires _ _).1
        (List.get_mem _ _))

def exposedAttachment (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    input.wireQuotient.Carrier :=
  input.quotientWire (input.attachment (layout.exposedPosition external))

/-- Boundary-class substitution into the complete coalesced-host site
context.  This is also the empty-proxy wire map. -/
noncomputable def exposedWireRenaming {signature : List Nat}
    {input : Input signature} (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site) :
    Fin input.pattern.val.exposedWires.length →
      Fin (host.compilerLeaf.inheritedWires.extend input.site).length :=
  fun external =>
    let position := layout.exposedPosition external
    host.compilerLeaf.siteWireIndex host.intrinsicPath
      (layout.exposedAttachment external)
      (input.quotientAttachment_visible hadmissible position)

theorem exposedWireRenaming_spec {signature : List Nat}
    {input : Input signature} (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    (external : Fin input.pattern.val.exposedWires.length) :
    (host.compilerLeaf.inheritedWires.extend input.site).get
        (layout.exposedWireRenaming hadmissible host external) =
      layout.exposedAttachment external := by
  let position := layout.exposedPosition external
  have hspec := host.compilerLeaf.siteWireIndex_spec host.intrinsicPath
    (input.quotientWire (input.attachment position))
    (input.quotientAttachment_visible hadmissible position)
  simpa only [exposedWireRenaming, exposedAttachment, position] using hspec

noncomputable def terminalExternal
    (input : Input signature)
    {body : Region signature outer rels} {path : List Nat}
    (patternPath : Region.ContextPath body path)
    (terminal : Fin input.binderSpine.proxyCount)
    (terminal_is_last : terminal.val = input.binderSpine.proxyCount - 1)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      (input.binderSpine.proxy terminal) patternPath)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    Fin patternLeaf.inheritedWires.length →
      Fin input.pattern.val.exposedWires.length :=
  Region.ContextPath.CompilerLeaf.inheritedExposedEquiv input.pattern
    input.binderSpine input.terminalBody hnonempty patternPath terminal
    terminal_is_last patternLeaf

theorem terminalExternal_spec
    (input : Input signature)
    {body : Region signature outer rels} {path : List Nat}
    (patternPath : Region.ContextPath body path)
    (terminal : Fin input.binderSpine.proxyCount)
    (terminal_is_last : terminal.val = input.binderSpine.proxyCount - 1)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      (input.binderSpine.proxy terminal) patternPath)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin patternLeaf.inheritedWires.length) :
    input.pattern.val.exposedWires.get
        (@terminalExternal signature outer rels input body path patternPath
          terminal terminal_is_last patternLeaf hnonempty index) =
      patternLeaf.inheritedWires.get index := by
  exact patternLeaf.inheritedExposedEquiv_spec input.pattern
    input.binderSpine input.terminalBody hnonempty patternPath terminal
    terminal_is_last index

/-- Capture-avoiding wire transport from the terminal pattern compiler
context into the coalesced host's complete site context. -/
noncomputable def terminalWireRenaming {signature : List Nat}
    {input : Input signature} (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {body : Region signature outer rels} {path : List Nat}
    (patternPath : Region.ContextPath body path)
    (terminal : Fin input.binderSpine.proxyCount)
    (terminal_is_last : terminal.val = input.binderSpine.proxyCount - 1)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      (input.binderSpine.proxy terminal) patternPath)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    Fin patternLeaf.inheritedWires.length →
      Fin (host.compilerLeaf.inheritedWires.extend input.site).length :=
  fun index =>
    let externalMap : Fin patternLeaf.inheritedWires.length →
        Fin input.pattern.val.exposedWires.length :=
      @terminalExternal signature outer rels input body path patternPath
        terminal terminal_is_last patternLeaf hnonempty
    let external := externalMap index
    layout.exposedWireRenaming hadmissible host external

theorem terminalWireRenaming_target_spec {signature : List Nat}
    {input : Input signature} (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {body : Region signature outer rels} {path : List Nat}
    (patternPath : Region.ContextPath body path)
    (terminal : Fin input.binderSpine.proxyCount)
    (terminal_is_last : terminal.val = input.binderSpine.proxyCount - 1)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      (input.binderSpine.proxy terminal) patternPath)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin patternLeaf.inheritedWires.length) :
    ∃ external : Fin input.pattern.val.exposedWires.length,
      (host.compilerLeaf.inheritedWires.extend input.site).get
          (layout.terminalWireRenaming hadmissible host patternPath terminal
            terminal_is_last patternLeaf hnonempty index) =
        layout.exposedAttachment external := by
  let externalMap : Fin patternLeaf.inheritedWires.length →
      Fin input.pattern.val.exposedWires.length :=
    @terminalExternal signature outer rels input body path patternPath terminal
      terminal_is_last patternLeaf hnonempty
  let external := externalMap index
  refine ⟨external, ?_⟩
  simpa only [terminalWireRenaming, externalMap, external] using
    layout.exposedWireRenaming_spec hadmissible host external

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

theorem boundaryWires_nodup (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    (layout.boundaryWires quotient).Nodup := by
  unfold boundaryWires
  apply List.Pairwise.map
    (R := fun left right => left ≠ right)
    (S := fun left right => left ≠ right)
  · intro left right hne heq
    apply hne
    apply Fin.ext
    exact (List.getElem_inj input.pattern.val.exposedWires_nodup).mp (by
      simpa only [List.get_eq_getElem] using heq)
  · exact List.Pairwise.filter _ (allFin_nodup _)

theorem boundaryEndpoints_nodup (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    (layout.boundaryEndpoints quotient).Nodup := by
  unfold boundaryEndpoints
  apply List.Pairwise.map
    (R := fun left right => left ≠ right)
    (S := fun left right => left ≠ right)
    layout.mapPatternEndpoint
    (fun left right hne heq => hne
      (layout.mapPatternEndpoint_injective heq))
  exact endpointLists_nodup
      ⟨input.pattern.val.diagram,
        input.pattern.property.diagram_well_formed⟩
      (layout.boundaryWires quotient) (layout.boundaryWires_nodup quotient)

theorem mem_boundaryEndpoints (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier)
    (endpoint : CEndpoint layout.nodeCount) :
    endpoint ∈ layout.boundaryEndpoints quotient ↔
      ∃ external : Fin input.pattern.val.exposedWires.length,
        layout.exposedAttachment external = quotient ∧
          ∃ original : CEndpoint input.pattern.val.diagram.nodeCount,
            original ∈ (input.pattern.val.diagram.wires
                (input.pattern.val.exposedWires.get external)).endpoints ∧
              layout.mapPatternEndpoint original = endpoint := by
  simp only [boundaryEndpoints]
  rw [List.mem_map]
  constructor
  · rintro ⟨original, horiginal, heq⟩
    rw [List.mem_flatMap] at horiginal
    obtain ⟨wire, hwire, hendpoint⟩ := horiginal
    rw [boundaryWires, List.mem_map] at hwire
    obtain ⟨external, hexternal, hget⟩ := hwire
    rw [List.mem_filter] at hexternal
    exact ⟨external, (decide_eq_true_iff.mp hexternal.2), original,
      by simpa only [hget] using hendpoint, heq⟩
  · rintro ⟨external, heq, original, horiginal, rfl⟩
    refine ⟨original, ?_, rfl⟩
    rw [List.mem_flatMap]
    refine ⟨input.pattern.val.exposedWires.get external, ?_, horiginal⟩
    rw [boundaryWires, List.mem_map]
    refine ⟨external, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨mem_allFin external, decide_eq_true_iff.mpr heq⟩

def mapFrameRegion (layout : PlugLayout input) :
    CRegion input.frame.val.regionCount → CRegion layout.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (layout.frameRegion parent)
  | .bubble parent arity => .bubble (layout.frameRegion parent) arity

def mapFrameNode (layout : PlugLayout input) :
    CNode input.frame.val.regionCount → CNode layout.regionCount
  | .term region freePorts term =>
      .term (layout.frameRegion region) freePorts term
  | .atom region binder =>
      .atom (layout.frameRegion region) (layout.frameRegion binder)
  | .named region definition arity =>
      .named (layout.frameRegion region) definition arity

@[simp] theorem mapFrameNode_region (layout : PlugLayout input)
    (node : CNode input.frame.val.regionCount) :
    (layout.mapFrameNode node).region = layout.frameRegion node.region := by
  cases node <;> rfl

@[simp] theorem mapPatternNode_region (layout : PlugLayout input)
    (node : CNode input.pattern.val.diagram.regionCount) :
    (layout.mapPatternNode node).region = layout.bodyRegion node.region := by
  cases node <;> rfl

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

def plugRaw (layout : PlugLayout input) : ConcreteDiagram where
  regionCount := layout.regionCount
  nodeCount := layout.nodeCount
  wireCount := layout.wireCount
  root := layout.frameRegion input.frame.val.root
  regions := layout.plugRegion
  nodes := layout.plugNode
  wires := layout.plugWire

def mapFrameOccurrence (layout : PlugLayout input) :
    ConcreteElaboration.LocalOccurrence input.coalesceFrameRaw.regionCount
        input.coalesceFrameRaw.nodeCount →
      ConcreteElaboration.LocalOccurrence layout.plugRaw.regionCount
        layout.plugRaw.nodeCount
  | .node node => .node (layout.frameNode node)
  | .child region => .child (layout.frameRegion region)

def mapPatternOccurrence (layout : PlugLayout input) :
    ConcreteElaboration.LocalOccurrence input.pattern.val.diagram.regionCount
        input.pattern.val.diagram.nodeCount →
      ConcreteElaboration.LocalOccurrence layout.plugRaw.regionCount
        layout.plugRaw.nodeCount
  | .node node => .node (layout.patternNode node)
  | .child region => .child (layout.bodyRegion region)

/-- The output site's direct occurrences, presented in semantic insertion
order: existing coalesced-host material followed by terminal pattern material.
The executable elaborator may enumerate the same finite set in a different
node/child block order; `ItemSeqIso.permute` accounts for that order only. -/
def semanticSiteOccurrences (layout : PlugLayout input) :
    List (ConcreteElaboration.LocalOccurrence layout.plugRaw.regionCount
      layout.plugRaw.nodeCount) :=
  (ConcreteElaboration.localOccurrences input.coalesceFrameRaw input.site).map
      layout.mapFrameOccurrence ++
    (ConcreteElaboration.localOccurrences input.pattern.val.diagram
      input.binderSpine.bodyContainer).map layout.mapPatternOccurrence

@[simp] theorem plugWire_quotientBlockWire (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) :
    layout.plugWire (layout.quotientBlockWire wire) = {
      scope := layout.frameRegion (input.coalescedScope wire)
      endpoints :=
        (input.coalescedEndpoints wire).map layout.mapFrameEndpoint ++
          layout.boundaryEndpoints wire
    } := by
  simp [plugWire, quotientBlockWire]

@[simp] theorem plugWire_internalBlockWire (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (wire : layout.internalWires.Carrier) :
    layout.plugWire (layout.internalBlockWire wire) =
      layout.mapPatternWire (input.pattern.val.diagram.wires
        (layout.internalWires.origin wire)) := by
  simp [plugWire, internalBlockWire]

@[simp] theorem plugRegion_frameRegion (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    layout.plugRegion (layout.frameRegion region) =
      layout.mapFrameRegion (input.frame.val.regions region) := by
  simp [plugRegion, frameRegion]

@[simp] theorem plugRegion_materialRegion (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    layout.plugRegion (layout.materialRegion material) =
      layout.mapPatternRegion (input.pattern.val.diagram.regions
        (layout.materialRegions.origin material)) := by
  simp [plugRegion, materialRegion]

@[simp] theorem plugNode_frameNode (layout : PlugLayout input)
    (node : Fin input.frame.val.nodeCount) :
    layout.plugNode (layout.frameNode node) =
      layout.mapFrameNode (input.frame.val.nodes node) := by
  simp [plugNode, frameNode]

@[simp] theorem plugNode_patternNode (layout : PlugLayout input)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    layout.plugNode (layout.patternNode node) =
      layout.mapPatternNode (input.pattern.val.diagram.nodes node) := by
  simp [plugNode, patternNode]

theorem mapFrameOccurrence_mem_localOccurrences (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.coalesceFrameRaw.regionCount input.coalesceFrameRaw.nodeCount) :
    layout.mapFrameOccurrence occurrence ∈
        ConcreteElaboration.localOccurrences layout.plugRaw
          (layout.frameRegion region) ↔
      occurrence ∈ ConcreteElaboration.localOccurrences
        input.coalesceFrameRaw region := by
  cases occurrence with
  | node node =>
      simp only [mapFrameOccurrence]
      rw [ConcreteElaboration.mem_localOccurrences_node,
        ConcreteElaboration.mem_localOccurrences_node]
      change (layout.plugNode (layout.frameNode node)).region =
        layout.frameRegion region ↔
          (input.coalesceFrameRaw.nodes node).region = region
      rw [layout.plugNode_frameNode, layout.mapFrameNode_region]
      simp only [coalesceFrameRaw_nodes, layout.frameRegion_eq_iff]
      rfl
  | child child =>
      simp only [mapFrameOccurrence]
      rw [ConcreteElaboration.mem_localOccurrences_child,
        ConcreteElaboration.mem_localOccurrences_child]
      change (layout.plugRegion (layout.frameRegion child)).parent? =
        some (layout.frameRegion region) ↔
          (input.coalesceFrameRaw.regions child).parent? = some region
      rw [layout.plugRegion_frameRegion]
      cases hregion : input.frame.val.regions child <;>
        simp [hregion, mapFrameRegion, CRegion.parent?,
          layout.frameRegion_eq_iff]

theorem bodyRegion_parent_exact (layout : PlugLayout input)
    (region parent : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region)
    (hparent : (input.pattern.val.diagram.regions region).parent? = some parent) :
    (layout.plugRaw.regions (layout.bodyRegion region)).parent? =
      some (layout.bodyRegion parent) := by
  rw [layout.bodyRegion_material region hmaterial]
  change (layout.plugRegion (layout.materialRegion
    (layout.materialIndex region hmaterial))).parent? = _
  rw [layout.plugRegion_materialRegion]
  have horigin : layout.materialRegions.origin
      (layout.materialIndex region hmaterial) = region := by
    exact layout.materialRegions.origin_index region
      ((layout.materialRegions_survives_iff region).2 hmaterial)
  rw [horigin]
  cases hregion : input.pattern.val.diagram.regions region with
  | sheet =>
      rw [hregion] at hparent
      contradiction
  | cut actualParent =>
      simp only [hregion, CRegion.parent?] at hparent
      cases hparent
      rfl
  | bubble actualParent arity =>
      simp only [hregion, CRegion.parent?] at hparent
      cases hparent
      rfl

theorem plugRaw_bodyRegion_cut (layout : PlugLayout input)
    (child parent : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion child)
    (hchild : input.pattern.val.diagram.regions child = .cut parent) :
    layout.plugRaw.regions (layout.bodyRegion child) =
      .cut (layout.bodyRegion parent) := by
  rw [layout.bodyRegion_material child hmaterial]
  change layout.plugRegion
      (layout.materialRegion (layout.materialIndex child hmaterial)) = _
  rw [layout.plugRegion_materialRegion]
  have horigin : layout.materialRegions.origin
      (layout.materialIndex child hmaterial) = child :=
    layout.materialRegions.origin_index child
      ((layout.materialRegions_survives_iff child).2 hmaterial)
  rw [horigin, hchild]
  rfl

theorem plugRaw_bodyRegion_bubble (layout : PlugLayout input)
    (child parent : Fin input.pattern.val.diagram.regionCount)
    (arity : Nat)
    (hmaterial : input.binderSpine.IsMaterialRegion child)
    (hchild : input.pattern.val.diagram.regions child = .bubble parent arity) :
    layout.plugRaw.regions (layout.bodyRegion child) =
      .bubble (layout.bodyRegion parent) arity := by
  rw [layout.bodyRegion_material child hmaterial]
  change layout.plugRegion
      (layout.materialRegion (layout.materialIndex child hmaterial)) = _
  rw [layout.plugRegion_materialRegion]
  have horigin : layout.materialRegions.origin
      (layout.materialIndex child hmaterial) = child :=
    layout.materialRegions.origin_index child
      ((layout.materialRegions_survives_iff child).2 hmaterial)
  rw [horigin, hchild]
  rfl

theorem plugRaw_frameRegion_cut (layout : PlugLayout input)
    (child parent : Fin input.coalesceFrameRaw.regionCount)
    (hchild : input.coalesceFrameRaw.regions child = .cut parent) :
    layout.plugRaw.regions (layout.frameRegion child) =
      .cut (layout.frameRegion parent) := by
  change layout.plugRegion (layout.frameRegion child) = _
  rw [layout.plugRegion_frameRegion]
  change layout.mapFrameRegion (input.coalesceFrameRaw.regions child) = _
  rw [hchild]
  rfl

theorem plugRaw_frameRegion_bubble (layout : PlugLayout input)
    (child parent : Fin input.coalesceFrameRaw.regionCount)
    (arity : Nat)
    (hchild : input.coalesceFrameRaw.regions child = .bubble parent arity) :
    layout.plugRaw.regions (layout.frameRegion child) =
      .bubble (layout.frameRegion parent) arity := by
  change layout.plugRegion (layout.frameRegion child) = _
  rw [layout.plugRegion_frameRegion]
  change layout.mapFrameRegion (input.coalesceFrameRaw.regions child) = _
  rw [hchild]
  rfl

theorem bodyRegion_parent_encloses (layout : PlugLayout input)
    (region parent : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region)
    (hparent : (input.pattern.val.diagram.regions region).parent? = some parent) :
    layout.plugRaw.Encloses (layout.bodyRegion parent)
      (layout.bodyRegion region) := by
  refine ⟨⟨1, by
    simp only [plugRaw, regionCount]
    have := input.frame.val.root.isLt
    omega⟩, ?_⟩
  simp only [ConcreteDiagram.climb,
    layout.bodyRegion_parent_exact region parent hmaterial hparent]

theorem nonmaterial_parent_eq_bodyContainer (input : Input signature)
    (region parent : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region)
    (hparent : (input.pattern.val.diagram.regions region).parent? = some parent)
    (hparentNonmaterial : ¬ input.binderSpine.IsMaterialRegion parent) :
    parent = input.binderSpine.bodyContainer := by
  by_cases hroot : parent = input.pattern.val.diagram.root
  · by_cases hzero : input.binderSpine.proxyCount = 0
    · exact hroot.trans
        (input.binderSpine.body_eq_root_of_empty hzero).symm
    · have hfirst := input.terminalBody.root_direct_child hzero region (by
        simpa only [hroot] using hparent)
      exact False.elim (hmaterial.2 ⟨0, Nat.pos_of_ne_zero hzero⟩ hfirst)
  · have hproxy : ∃ index : Fin input.binderSpine.proxyCount,
        parent = input.binderSpine.proxy index := by
      exact Classical.byContradiction fun hnone => hparentNonmaterial ⟨hroot, by
        intro index heq
        exact hnone ⟨index, heq⟩⟩
    obtain ⟨index, hindex⟩ := hproxy
    by_cases hnonterminal : index.val + 1 < input.binderSpine.proxyCount
    · have hnext := input.terminalBody.nonterminal_direct_child
        index hnonterminal region (by simpa only [hindex] using hparent)
      exact False.elim (hmaterial.2 ⟨index.val + 1, hnonterminal⟩ hnext)
    · have hcount : index.val + 1 = input.binderSpine.proxyCount := by
        have := index.isLt
        omega
      have hnonzero : input.binderSpine.proxyCount ≠ 0 := by
        have := index.isLt
        omega
      let terminal : Fin input.binderSpine.proxyCount :=
        ⟨input.binderSpine.proxyCount - 1, by omega⟩
      have hterminal : index = terminal := by
        apply Fin.ext
        simp only [terminal]
        omega
      rw [hindex, hterminal]
      exact (input.binderSpine.body_eq_terminal_of_nonempty hnonzero).symm

/-- Every direct child of the designated body container is material.  For a
nonempty spine the container is the last proxy, so there is no further proxy
child; for an empty spine every proper region is material. -/
theorem directChildOfBody_material (input : Input signature)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hparent : (input.pattern.val.diagram.regions region).parent? =
      some input.binderSpine.bodyContainer) :
    input.binderSpine.IsMaterialRegion region := by
  have hneRoot : region ≠ input.pattern.val.diagram.root := by
    intro heq
    subst region
    rw [input.pattern.property.diagram_well_formed.root_is_sheet] at hparent
    simp [CRegion.parent?] at hparent
  refine ⟨hneRoot, ?_⟩
  intro index heq
  subst region
  rw [input.binderSpine.proxy_region] at hparent
  simp only [CRegion.parent?] at hparent
  split at hparent
  · rename_i hzero
    have hnonempty : input.binderSpine.proxyCount ≠ 0 := by
      have := index.isLt
      omega
    have hbody := input.binderSpine.body_eq_terminal_of_nonempty hnonempty
    rw [hbody] at hparent
    exact input.binderSpine.proxy_ne_root
      ⟨input.binderSpine.proxyCount - 1, by omega⟩
      (Option.some.inj hparent).symm
  · rename_i hnonzero
    have hcountNonzero : input.binderSpine.proxyCount ≠ 0 := by
      have := index.isLt
      omega
    have hbody := input.binderSpine.body_eq_terminal_of_nonempty hcountNonzero
    rw [hbody] at hparent
    have hindices := input.binderSpine.proxy_injective
      (Option.some.inj hparent)
    have hvals := congrArg Fin.val hindices
    simp only at hvals
    have := index.isLt
    omega

/-- A proxy can only have the sheet or another proxy as parent, so every
direct child of retained material is itself retained material. -/
theorem directChildOfMaterial_material (input : Input signature)
    (parent child : Fin input.pattern.val.diagram.regionCount)
    (hparentMaterial : input.binderSpine.IsMaterialRegion parent)
    (hchild : (input.pattern.val.diagram.regions child).parent? =
      some parent) :
    input.binderSpine.IsMaterialRegion child := by
  have hchildNeRoot : child ≠ input.pattern.val.diagram.root := by
    intro heq
    subst child
    rw [input.pattern.property.diagram_well_formed.root_is_sheet] at hchild
    simp [CRegion.parent?] at hchild
  refine ⟨hchildNeRoot, ?_⟩
  intro index heq
  subst child
  rw [input.binderSpine.proxy_region] at hchild
  simp only [CRegion.parent?] at hchild
  split at hchild
  · exact hparentMaterial.1 (Option.some.inj hchild).symm
  · rename_i hnonzero
    let previous : Fin input.binderSpine.proxyCount :=
      ⟨index.val - 1, by omega⟩
    exact hparentMaterial.2 previous (Option.some.inj hchild).symm

theorem patternNode_region_material_or_bodyContainer
    (input : Input signature)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    input.binderSpine.IsMaterialRegion
        (input.pattern.val.diagram.nodes node).region ∨
      (input.pattern.val.diagram.nodes node).region =
        input.binderSpine.bodyContainer := by
  let region := (input.pattern.val.diagram.nodes node).region
  by_cases hmaterial : input.binderSpine.IsMaterialRegion region
  · exact Or.inl hmaterial
  · right
    by_cases hroot : region = input.pattern.val.diagram.root
    · by_cases hzero : input.binderSpine.proxyCount = 0
      · exact hroot.trans
          (input.binderSpine.body_eq_root_of_empty hzero).symm
      · exact False.elim
          (input.terminalBody.root_has_no_nodes hzero node hroot)
    · have hproxy : ∃ index : Fin input.binderSpine.proxyCount,
          region = input.binderSpine.proxy index := by
        exact Classical.byContradiction fun hnone => hmaterial ⟨hroot, by
          intro index heq
          exact hnone ⟨index, heq⟩⟩
      obtain ⟨index, hproxy⟩ := hproxy
      by_cases hnonterminal :
          index.val + 1 < input.binderSpine.proxyCount
      · exact False.elim
          (input.terminalBody.nonterminal_has_no_nodes
            index hnonterminal node hproxy)
      · have hnonzero : input.binderSpine.proxyCount ≠ 0 := by
          have := index.isLt
          omega
        let terminal : Fin input.binderSpine.proxyCount :=
          ⟨input.binderSpine.proxyCount - 1, by omega⟩
        have hterminal : index = terminal := by
          apply Fin.ext
          simp only [terminal]
          have := index.isLt
          omega
        change region = input.binderSpine.bodyContainer
        rw [hproxy, hterminal]
        exact (input.binderSpine.body_eq_terminal_of_nonempty hnonzero).symm

theorem patternInternalWire_scope_material_or_bodyContainer
    (input : Input signature)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (hinternal : wire ∉ input.pattern.val.exposedWires) :
    input.binderSpine.IsMaterialRegion
        (input.pattern.val.diagram.wires wire).scope ∨
      (input.pattern.val.diagram.wires wire).scope =
        input.binderSpine.bodyContainer := by
  let scope := (input.pattern.val.diagram.wires wire).scope
  by_cases hmaterial : input.binderSpine.IsMaterialRegion scope
  · exact Or.inl hmaterial
  · right
    have hnotBoundary : wire ∉ input.pattern.val.boundary := by
      intro hboundary
      exact hinternal
        ((OpenConcreteDiagram.mem_exposedWires input.pattern.val wire).2
          hboundary)
    by_cases hroot : scope = input.pattern.val.diagram.root
    · by_cases hzero : input.binderSpine.proxyCount = 0
      · exact hroot.trans
          (input.binderSpine.body_eq_root_of_empty hzero).symm
      · exact False.elim
          (input.terminalBody.root_has_no_nonboundary_wires hzero wire
            hnotBoundary hroot)
    · have hproxy : ∃ index : Fin input.binderSpine.proxyCount,
          scope = input.binderSpine.proxy index := by
        exact Classical.byContradiction fun hnone => hmaterial ⟨hroot, by
          intro index heq
          exact hnone ⟨index, heq⟩⟩
      obtain ⟨index, hproxy⟩ := hproxy
      by_cases hnonterminal :
          index.val + 1 < input.binderSpine.proxyCount
      · exact False.elim
          (input.terminalBody.nonterminal_has_no_nonboundary_wires
            index hnonterminal wire hnotBoundary hproxy)
      · have hnonzero : input.binderSpine.proxyCount ≠ 0 := by
          have := index.isLt
          omega
        let terminal : Fin input.binderSpine.proxyCount :=
          ⟨input.binderSpine.proxyCount - 1, by omega⟩
        have hterminal : index = terminal := by
          apply Fin.ext
          simp only [terminal]
          have := index.isLt
          omega
        change scope = input.binderSpine.bodyContainer
        rw [hproxy, hterminal]
        exact (input.binderSpine.body_eq_terminal_of_nonempty hnonzero).symm

theorem mapPatternOccurrence_mem_localOccurrences_of_mem
    (layout : PlugLayout input)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.pattern.val.diagram.regionCount
      input.pattern.val.diagram.nodeCount)
    (hmem : occurrence ∈ ConcreteElaboration.localOccurrences
      input.pattern.val.diagram input.binderSpine.bodyContainer) :
    layout.mapPatternOccurrence occurrence ∈
      ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion input.site) := by
  cases occurrence with
  | node node =>
      have hregion :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hmem
      simp only [mapPatternOccurrence]
      rw [ConcreteElaboration.mem_localOccurrences_node]
      change (layout.plugNode (layout.patternNode node)).region =
        layout.frameRegion input.site
      rw [layout.plugNode_patternNode, layout.mapPatternNode_region, hregion,
        layout.bodyRegion_bodyContainer]
  | child child =>
      have hparent :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hmem
      have hmaterial := directChildOfBody_material input child hparent
      simp only [mapPatternOccurrence]
      rw [ConcreteElaboration.mem_localOccurrences_child]
      exact (layout.bodyRegion_parent_exact child
        input.binderSpine.bodyContainer hmaterial hparent).trans
          (congrArg some layout.bodyRegion_bodyContainer)

theorem semanticSiteOccurrences_subset (layout : PlugLayout input) :
    ∀ occurrence, occurrence ∈ layout.semanticSiteOccurrences →
      occurrence ∈ ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion input.site) := by
  intro occurrence hmem
  rw [semanticSiteOccurrences, List.mem_append] at hmem
  rcases hmem with hframe | hpattern
  · rw [List.mem_map] at hframe
    rcases hframe with ⟨source, hsource, rfl⟩
    exact (layout.mapFrameOccurrence_mem_localOccurrences input.site source).2
      hsource
  · rw [List.mem_map] at hpattern
    rcases hpattern with ⟨source, hsource, rfl⟩
    exact layout.mapPatternOccurrence_mem_localOccurrences_of_mem source hsource

theorem semanticSiteOccurrences_complete (layout : PlugLayout input) :
    ∀ occurrence,
      occurrence ∈ ConcreteElaboration.localOccurrences layout.plugRaw
          (layout.frameRegion input.site) →
        occurrence ∈ layout.semanticSiteOccurrences := by
  intro occurrence hmem
  cases occurrence with
  | node node =>
      revert hmem
      refine Fin.addCases (m := input.frame.val.nodeCount)
        (n := input.pattern.val.diagram.nodeCount) (fun frameNode => ?_)
        (fun patternNode => ?_) node
      · intro hmem
        apply List.mem_append_left
        rw [List.mem_map]
        refine ⟨.node frameNode, ?_, rfl⟩
        exact (layout.mapFrameOccurrence_mem_localOccurrences input.site
          (.node frameNode)).1 hmem
      · intro hmem
        have hregion :=
          (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hmem
        change (layout.plugNode (layout.patternNode patternNode)).region =
          layout.frameRegion input.site at hregion
        rw [layout.plugNode_patternNode, layout.mapPatternNode_region]
          at hregion
        rcases patternNode_region_material_or_bodyContainer input patternNode with
          hmaterial | hbody
        · rw [layout.bodyRegion_material _ hmaterial] at hregion
          exact False.elim
            (layout.frameRegion_ne_materialRegion input.site _ hregion.symm)
        · apply List.mem_append_right
          rw [List.mem_map]
          refine ⟨.node patternNode, ?_, rfl⟩
          exact (ConcreteElaboration.mem_localOccurrences_node _ _ _).2 hbody
  | child child =>
      revert hmem
      refine Fin.addCases (m := input.frame.val.regionCount)
        (n := layout.materialRegions.count) (fun frameChild => ?_)
        (fun materialChild => ?_) child
      · intro hmem
        apply List.mem_append_left
        rw [List.mem_map]
        refine ⟨.child frameChild, ?_, rfl⟩
        exact (layout.mapFrameOccurrence_mem_localOccurrences input.site
          (.child frameChild)).1 hmem
      · let original := layout.materialRegions.origin materialChild
        intro hmem
        have hmaterial : input.binderSpine.IsMaterialRegion original :=
          (layout.materialRegions_survives_iff original).1
            (layout.materialRegions.origin_survives materialChild)
        have houtput :=
          (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hmem
        change (layout.plugRegion (layout.materialRegion materialChild)).parent? =
          some (layout.frameRegion input.site) at houtput
        rw [layout.plugRegion_materialRegion] at houtput
        cases hregion : input.pattern.val.diagram.regions original with
        | sheet =>
            exact False.elim (hmaterial.1
              (input.pattern.property.diagram_well_formed.only_root_is_sheet
                original hregion))
        | cut parent =>
            have hparent :
                (input.pattern.val.diagram.regions original).parent? =
                  some parent := by simp [hregion, CRegion.parent?]
            have hmapped : layout.bodyRegion parent =
                layout.frameRegion input.site := by
              change (layout.mapPatternRegion
                (input.pattern.val.diagram.regions original)).parent? =
                  some (layout.frameRegion input.site) at houtput
              rw [hregion] at houtput
              exact Option.some.inj houtput
            have hparentBody : parent = input.binderSpine.bodyContainer := by
              by_cases hparentMaterial :
                  input.binderSpine.IsMaterialRegion parent
              · rw [layout.bodyRegion_material parent hparentMaterial] at hmapped
                exact False.elim
                  (layout.frameRegion_ne_materialRegion input.site _ hmapped.symm)
              · exact nonmaterial_parent_eq_bodyContainer input original parent
                  hmaterial hparent hparentMaterial
            apply List.mem_append_right
            rw [List.mem_map]
            refine ⟨.child original, ?_, ?_⟩
            · exact (ConcreteElaboration.mem_localOccurrences_child _ _ _).2
                (hparentBody ▸ hparent)
            · exact congrArg ConcreteElaboration.LocalOccurrence.child
                (layout.bodyRegion_origin materialChild)
        | bubble parent arity =>
            have hparent :
                (input.pattern.val.diagram.regions original).parent? =
                  some parent := by simp [hregion, CRegion.parent?]
            have hmapped : layout.bodyRegion parent =
                layout.frameRegion input.site := by
              change (layout.mapPatternRegion
                (input.pattern.val.diagram.regions original)).parent? =
                  some (layout.frameRegion input.site) at houtput
              rw [hregion] at houtput
              exact Option.some.inj houtput
            have hparentBody : parent = input.binderSpine.bodyContainer := by
              by_cases hparentMaterial :
                  input.binderSpine.IsMaterialRegion parent
              · rw [layout.bodyRegion_material parent hparentMaterial] at hmapped
                exact False.elim
                  (layout.frameRegion_ne_materialRegion input.site _ hmapped.symm)
              · exact nonmaterial_parent_eq_bodyContainer input original parent
                  hmaterial hparent hparentMaterial
            apply List.mem_append_right
            rw [List.mem_map]
            refine ⟨.child original, ?_, ?_⟩
            · exact (ConcreteElaboration.mem_localOccurrences_child _ _ _).2
                (hparentBody ▸ hparent)
            · exact congrArg ConcreteElaboration.LocalOccurrence.child
                (layout.bodyRegion_origin materialChild)

theorem mapFrameOccurrence_injective (layout : PlugLayout input) :
    Function.Injective layout.mapFrameOccurrence := by
  intro left right heq
  cases left <;> cases right
  · exact congrArg ConcreteElaboration.LocalOccurrence.node
      (layout.frameNode_injective
        (ConcreteElaboration.LocalOccurrence.node.inj heq))
  · contradiction
  · contradiction
  · exact congrArg ConcreteElaboration.LocalOccurrence.child
      (layout.frameRegion_injective
        (ConcreteElaboration.LocalOccurrence.child.inj heq))

def frameSemanticOccurrences (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount) :
    List (ConcreteElaboration.LocalOccurrence layout.plugRaw.regionCount
      layout.plugRaw.nodeCount) :=
  (ConcreteElaboration.localOccurrences input.coalesceFrameRaw region).map
    layout.mapFrameOccurrence

theorem frameSemanticOccurrences_complete (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site) :
    ∀ occurrence, occurrence ∈ ConcreteElaboration.localOccurrences
        layout.plugRaw (layout.frameRegion region) →
      ∃ original, original ∈ ConcreteElaboration.localOccurrences
          input.coalesceFrameRaw region ∧
        layout.mapFrameOccurrence original = occurrence := by
  intro occurrence hmem
  cases occurrence with
  | node node =>
      revert hmem
      refine Fin.addCases (m := input.frame.val.nodeCount)
        (n := input.pattern.val.diagram.nodeCount) (fun frameNode => ?_)
        (fun patternNode => ?_) node
      · intro hmem
        exact ⟨.node frameNode,
          (layout.mapFrameOccurrence_mem_localOccurrences region
            (.node frameNode)).1 hmem, rfl⟩
      · intro hmem
        have htarget :=
          (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hmem
        change (layout.plugNode (layout.patternNode patternNode)).region =
          layout.frameRegion region at htarget
        rw [layout.plugNode_patternNode, layout.mapPatternNode_region] at htarget
        rcases patternNode_region_material_or_bodyContainer input patternNode with
          hmaterial | hbody
        · rw [layout.bodyRegion_material _ hmaterial] at htarget
          exact False.elim
            (layout.frameRegion_ne_materialRegion region _ htarget.symm)
        · rw [hbody, layout.bodyRegion_bodyContainer] at htarget
          exact False.elim (hne (layout.frameRegion_injective htarget).symm)
  | child child =>
      revert hmem
      refine Fin.addCases (m := input.frame.val.regionCount)
        (n := layout.materialRegions.count) (fun frameChild => ?_)
        (fun materialChild => ?_) child
      · intro hmem
        exact ⟨.child frameChild,
          (layout.mapFrameOccurrence_mem_localOccurrences region
            (.child frameChild)).1 hmem, rfl⟩
      · intro hmem
        let original := layout.materialRegions.origin materialChild
        have horiginalMaterial : input.binderSpine.IsMaterialRegion original :=
          (layout.materialRegions_survives_iff original).1
            (layout.materialRegions.origin_survives materialChild)
        have htarget :=
          (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hmem
        change (layout.plugRegion (layout.materialRegion materialChild)).parent? =
          some (layout.frameRegion region) at htarget
        rw [layout.plugRegion_materialRegion] at htarget
        change (layout.mapPatternRegion
          (input.pattern.val.diagram.regions original)).parent? =
            some (layout.frameRegion region) at htarget
        cases hsource : input.pattern.val.diagram.regions original with
        | sheet =>
            exact False.elim (horiginalMaterial.1
              (input.pattern.property.diagram_well_formed.only_root_is_sheet
                original hsource))
        | cut parent =>
            have hparent : (input.pattern.val.diagram.regions original).parent? =
                some parent := by simp [hsource, CRegion.parent?]
            have hmapped : layout.bodyRegion parent = layout.frameRegion region :=
              Option.some.inj (by
                simpa [hsource, mapPatternRegion, CRegion.parent?] using htarget)
            by_cases hparentMaterial :
                input.binderSpine.IsMaterialRegion parent
            · rw [layout.bodyRegion_material parent hparentMaterial] at hmapped
              exact False.elim
                (layout.frameRegion_ne_materialRegion region _ hmapped.symm)
            · have hparentBody := nonmaterial_parent_eq_bodyContainer input
                original parent horiginalMaterial hparent hparentMaterial
              rw [hparentBody, layout.bodyRegion_bodyContainer] at hmapped
              exact False.elim (hne (layout.frameRegion_injective hmapped).symm)
        | bubble parent arity =>
            have hparent : (input.pattern.val.diagram.regions original).parent? =
                some parent := by simp [hsource, CRegion.parent?]
            have hmapped : layout.bodyRegion parent = layout.frameRegion region :=
              Option.some.inj (by
                simpa [hsource, mapPatternRegion, CRegion.parent?] using htarget)
            by_cases hparentMaterial :
                input.binderSpine.IsMaterialRegion parent
            · rw [layout.bodyRegion_material parent hparentMaterial] at hmapped
              exact False.elim
                (layout.frameRegion_ne_materialRegion region _ hmapped.symm)
            · have hparentBody := nonmaterial_parent_eq_bodyContainer input
                original parent horiginalMaterial hparent hparentMaterial
              rw [hparentBody, layout.bodyRegion_bodyContainer] at hmapped
              exact False.elim (hne (layout.frameRegion_injective hmapped).symm)

theorem frameSemanticOccurrences_nodup (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount) :
    (layout.frameSemanticOccurrences region).Nodup := by
  exact (ConcreteElaboration.localOccurrences_nodup
    input.coalesceFrameRaw region).map layout.mapFrameOccurrence
      (fun left right hne heq => hne (layout.mapFrameOccurrence_injective heq))

noncomputable def frameOccurrenceEquiv (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site) :
    FiniteEquiv
      (Fin (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        region).length)
      (Fin (ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion region)).length) :=
  listEmbeddingEquiv layout.mapFrameOccurrence
    (ConcreteElaboration.localOccurrences input.coalesceFrameRaw region)
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.frameRegion region))
    (ConcreteElaboration.localOccurrences_nodup _ _)
    (ConcreteElaboration.localOccurrences_nodup _ _)
    (fun occurrence hmem =>
      (layout.mapFrameOccurrence_mem_localOccurrences region occurrence).2 hmem)
    (layout.frameSemanticOccurrences_complete region hne)
    (fun left _ right _ heq => layout.mapFrameOccurrence_injective heq)

theorem frameOccurrenceEquiv_spec (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (index : Fin (ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw region).length) :
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.frameRegion region)).get
        (layout.frameOccurrenceEquiv region hne index) =
      layout.mapFrameOccurrence
        ((ConcreteElaboration.localOccurrences input.coalesceFrameRaw
          region).get index) := by
  exact listEmbeddingEquiv_spec layout.mapFrameOccurrence
    (ConcreteElaboration.localOccurrences input.coalesceFrameRaw region)
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.frameRegion region)) _ _ _ _ _ index

def frameSemanticWires (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount) :
    List (Fin layout.plugRaw.wireCount) :=
  (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw region).map
    layout.frameWire

theorem frameSemanticWires_subset (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount) :
    ∀ wire, wire ∈ layout.frameSemanticWires region →
      wire ∈ ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion region) := by
  intro wire hmem
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
  have hscope :=
    (ConcreteElaboration.mem_exactScopeWires input.coalesceFrameRaw region
      source).1 hsource
  rw [ConcreteElaboration.mem_exactScopeWires]
  change (layout.plugWire (layout.quotientBlockWire source)).scope = _
  rw [plugWire_quotientBlockWire]
  exact congrArg layout.frameRegion hscope

theorem frameSemanticWires_complete (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site) :
    ∀ wire, wire ∈ ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion region) →
      wire ∈ layout.frameSemanticWires region := by
  intro wire hmem
  revert hmem
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun frame => ?_)
    (fun internal => ?_) wire
  · intro hmem
    apply List.mem_map.mpr
    refine ⟨frame, ?_, rfl⟩
    apply (ConcreteElaboration.mem_exactScopeWires
      input.coalesceFrameRaw region frame).2
    rw [ConcreteElaboration.mem_exactScopeWires] at hmem
    change (layout.plugWire (layout.quotientBlockWire frame)).scope = _ at hmem
    rw [plugWire_quotientBlockWire] at hmem
    exact layout.frameRegion_injective hmem
  · intro hmem
    rw [ConcreteElaboration.mem_exactScopeWires] at hmem
    change (layout.plugWire (layout.internalBlockWire internal)).scope = _ at hmem
    rw [plugWire_internalBlockWire] at hmem
    simp only [mapPatternWire] at hmem
    let original := layout.internalWires.origin internal
    have hinternal : original ∉ input.pattern.val.exposedWires :=
      (layout.internalWires_survives_iff original).1
        (layout.internalWires.origin_survives internal)
    rcases patternInternalWire_scope_material_or_bodyContainer input original
        hinternal with hmaterial | hbody
    · rw [layout.bodyRegion_material _ hmaterial] at hmem
      exact False.elim
        (layout.frameRegion_ne_materialRegion region _ hmem.symm)
    · rw [hbody, layout.bodyRegion_bodyContainer] at hmem
      exact False.elim (hne (layout.frameRegion_injective hmem).symm)

theorem frameSemanticWires_nodup (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount) :
    (layout.frameSemanticWires region).Nodup := by
  exact (ConcreteElaboration.exactScopeWires_nodup
    input.coalesceFrameRaw region).map layout.frameWire
      (fun left right hne heq => hne (layout.frameWire_injective heq))

noncomputable def frameLocalWireEquiv (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site) :
    FiniteEquiv
      (Fin (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        region).length)
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion region)).length) :=
  listEmbeddingEquiv layout.frameWire
    (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw region)
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion region))
    (ConcreteElaboration.exactScopeWires_nodup _ _)
    (ConcreteElaboration.exactScopeWires_nodup _ _)
    (fun source hsource => layout.frameSemanticWires_subset region _
      (List.mem_map_of_mem hsource))
    (fun target htarget => List.mem_map.mp
      (layout.frameSemanticWires_complete region hne target htarget))
    (fun left _ right _ heq => layout.frameWire_injective heq)

theorem frameLocalWireEquiv_spec (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw region).length) :
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion region)).get
        (layout.frameLocalWireEquiv region hne index) =
      layout.frameWire
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          region).get index) := by
  exact listEmbeddingEquiv_spec layout.frameWire
    (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw region)
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion region)) _ _ _ _ _ index

@[simp] theorem ConcreteElaboration.WireContext.extend_get_outer
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount) (index : Fin context.length) :
    (context.extend region).get
        (Fin.cast (ConcreteElaboration.WireContext.length_extend context region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires diagram region).length index)) =
      context.get index := by
  simp [ConcreteElaboration.WireContext.extend]

@[simp] theorem ConcreteElaboration.WireContext.extend_get_local
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires diagram region).length) :
    (context.extend region).get
        (Fin.cast (ConcreteElaboration.WireContext.length_extend context region).symm
          (Fin.natAdd context.length index)) =
      (ConcreteElaboration.exactScopeWires diagram region).get index := by
  simp [ConcreteElaboration.WireContext.extend]

noncomputable def frameExtendedWireMap (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length) :
    Fin (sourceContext.extend region).length →
      Fin (targetContext.extend (layout.frameRegion region)).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend targetContext
        (layout.frameRegion region)).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion region)).length (outerMap outer))
        (fun localIndex => Fin.natAdd targetContext.length
          (layout.frameLocalWireEquiv region hne localIndex))
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext region)
          index))

def frameSourceExtendedWireMap (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length) :
    Fin (sourceContext.extend region).length →
      Fin (targetContext.length +
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          region).length) :=
  fun index =>
    Fin.addCases
      (fun outer => Fin.castAdd
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          region).length (outerMap outer))
      (fun localIndex => Fin.natAdd targetContext.length localIndex)
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend sourceContext region)
        index)

theorem frameSourceExtendedWireMap_eq (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length) :
    layout.frameSourceExtendedWireMap region sourceContext targetContext outerMap =
      extendWireRenaming outerMap
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            region).length ∘
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext region) := by
  funext index
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceContext region) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split <;>
    simp [frameSourceExtendedWireMap, split, extendWireRenaming]

theorem frameFinishRegion_renameWires_renameRelations
    (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (items : ItemSeq signature (sourceContext.extend region).length sourceRels) :
    ((ConcreteElaboration.finishRegion input.coalesceFrameRaw sourceContext region
        items).renameWires outerMap).renameRelations relationMap =
      .mk (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          region).length
        ((items.renameWires
          (layout.frameSourceExtendedWireMap region sourceContext targetContext
            outerMap)).renameRelations relationMap) := by
  simp only [ConcreteElaboration.finishRegion, Region.renameWires,
    Region.renameRelations, ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp]
  rw [layout.frameSourceExtendedWireMap_eq region sourceContext targetContext
    outerMap]

theorem frameExtendedWireMap_factor (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length) :
    (fun index =>
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend targetContext
          (layout.frameRegion region)).symm
        (extendWireEquiv (FiniteEquiv.refl (Fin targetContext.length))
          (layout.frameLocalWireEquiv region hne)
          (layout.frameSourceExtendedWireMap region sourceContext targetContext
            outerMap index))) =
      layout.frameExtendedWireMap region hne sourceContext targetContext
        outerMap := by
  funext index
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceContext region) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split <;>
    simp [frameExtendedWireMap, frameSourceExtendedWireMap, split,
      extendWireEquiv, FiniteEquiv.refl]

theorem frameExtendedWireMap_spec (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length)
    (outerSpec : ∀ index, targetContext.get (outerMap index) =
      layout.frameWire (sourceContext.get index))
    (index : Fin (sourceContext.extend region).length) :
    (targetContext.extend (layout.frameRegion region)).get
        (layout.frameExtendedWireMap region hne sourceContext targetContext
          outerMap index) =
      layout.frameWire ((sourceContext.extend region).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceContext region) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have hmap : layout.frameExtendedWireMap region hne sourceContext
          targetContext outerMap
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend sourceContext
              region).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
                region).length outer)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend targetContext
            (layout.frameRegion region)).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion region)).length (outerMap outer)) := by
      apply Fin.ext
      simp [frameExtendedWireMap]
    rw [hmap]
    simpa only [ConcreteElaboration.WireContext.extend_get_outer] using
      outerSpec outer
  · have hmap : layout.frameExtendedWireMap region hne sourceContext
          targetContext outerMap
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend sourceContext
              region).symm
            (Fin.natAdd sourceContext.length localIndex)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend targetContext
            (layout.frameRegion region)).symm
          (Fin.natAdd targetContext.length
            (layout.frameLocalWireEquiv region hne localIndex)) := by
      apply Fin.ext
      simp [frameExtendedWireMap]
    rw [hmap]
    simpa only [ConcreteElaboration.WireContext.extend_get_local] using
      layout.frameLocalWireEquiv_spec region hne localIndex

theorem mapPatternOccurrence_injective_on_body
    (layout : PlugLayout input) :
    ∀ left, left ∈ ConcreteElaboration.localOccurrences
        input.pattern.val.diagram input.binderSpine.bodyContainer →
      ∀ right, right ∈ ConcreteElaboration.localOccurrences
        input.pattern.val.diagram input.binderSpine.bodyContainer →
        layout.mapPatternOccurrence left = layout.mapPatternOccurrence right →
          left = right := by
  intro left hleft right hright heq
  cases left with
  | node leftNode =>
      cases right with
      | node rightNode =>
          exact congrArg ConcreteElaboration.LocalOccurrence.node
            (layout.patternNode_injective
              (ConcreteElaboration.LocalOccurrence.node.inj heq))
      | child rightChild => contradiction
  | child leftChild =>
      cases right with
      | node rightNode => contradiction
      | child rightChild =>
          have leftParent :=
            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hleft
          have rightParent :=
            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hright
          have leftMaterial := directChildOfBody_material input leftChild
            leftParent
          have rightMaterial := directChildOfBody_material input rightChild
            rightParent
          have hregions := ConcreteElaboration.LocalOccurrence.child.inj heq
          rw [layout.bodyRegion_material leftChild leftMaterial,
            layout.bodyRegion_material rightChild rightMaterial] at hregions
          have hindices := layout.materialRegion_injective hregions
          have horigins := congrArg layout.materialRegions.origin hindices
          simpa only [materialIndex, SurvivorDomain.origin_index] using
            congrArg ConcreteElaboration.LocalOccurrence.child horigins

theorem semanticSiteOccurrences_nodup (layout : PlugLayout input) :
    layout.semanticSiteOccurrences.Nodup := by
  rw [semanticSiteOccurrences, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (ConcreteElaboration.localOccurrences_nodup
      input.coalesceFrameRaw input.site).map layout.mapFrameOccurrence
        (fun left right hne heq => hne
          (layout.mapFrameOccurrence_injective heq))
  · let bodyOccurrences := ConcreteElaboration.localOccurrences
      input.pattern.val.diagram input.binderSpine.bodyContainer
    have mappedNodup : ∀ items : List
        (ConcreteElaboration.LocalOccurrence
          input.pattern.val.diagram.regionCount
          input.pattern.val.diagram.nodeCount),
        items.Nodup →
        (∀ occurrence, occurrence ∈ items → occurrence ∈ bodyOccurrences) →
        (items.map layout.mapPatternOccurrence).Nodup := by
      intro items hnodup hsubset
      induction items with
      | nil => simp
      | cons head tail ih =>
          rw [List.nodup_cons] at hnodup
          rw [List.map, List.nodup_cons]
          constructor
          · intro hmapped
            rw [List.mem_map] at hmapped
            rcases hmapped with ⟨other, hother, heq⟩
            have horiginal := layout.mapPatternOccurrence_injective_on_body
              head (hsubset head (by simp)) other
              (hsubset other (by simp [hother])) heq.symm
            exact hnodup.1 (horiginal ▸ hother)
          · exact ih hnodup.2 (by
              intro occurrence hoccurrence
              exact hsubset occurrence (by simp [hoccurrence]))
    exact mappedNodup bodyOccurrences
      (ConcreteElaboration.localOccurrences_nodup _ _)
      (fun _ hmem => hmem)
  · intro frameOccurrence hframe patternOccurrence hpattern heq
    rw [List.mem_map] at hframe hpattern
    rcases hframe with ⟨frameSource, hframeSource, rfl⟩
    rcases hpattern with ⟨patternSource, hpatternSource, rfl⟩
    cases frameSource with
    | node frameNode =>
        cases patternSource with
        | node patternNode =>
            exact layout.frameNode_ne_patternNode frameNode patternNode
              (ConcreteElaboration.LocalOccurrence.node.inj heq)
        | child patternChild => contradiction
    | child frameChild =>
        cases patternSource with
        | node patternNode => contradiction
        | child patternChild =>
            have patternParent :=
              (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
                hpatternSource
            have patternMaterial := directChildOfBody_material input
              patternChild patternParent
            have hregions := ConcreteElaboration.LocalOccurrence.child.inj heq
            rw [layout.bodyRegion_material patternChild patternMaterial]
              at hregions
            exact layout.frameRegion_ne_materialRegion frameChild _ hregions

/-- Canonical permutation from semantic insertion order to the executable
elaborator's node/child enumeration order at the plugged site. -/
def siteOccurrenceEquiv (layout : PlugLayout input) :
    FiniteEquiv (Fin layout.semanticSiteOccurrences.length)
      (Fin (ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion input.site)).length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (ConcreteElaboration.LocalOccurrence
      layout.plugRaw.regionCount layout.plugRaw.nodeCount))
    layout.semanticSiteOccurrences
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.frameRegion input.site))
    layout.semanticSiteOccurrences_nodup
    (ConcreteElaboration.localOccurrences_nodup _ _)
    (fun occurrence => ⟨
      fun htarget => layout.semanticSiteOccurrences_complete occurrence htarget,
      fun hsource => layout.semanticSiteOccurrences_subset occurrence hsource⟩)

theorem siteOccurrenceEquiv_spec (layout : PlugLayout input)
    (index : Fin layout.semanticSiteOccurrences.length) :
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.frameRegion input.site)).get
        (layout.siteOccurrenceEquiv index) =
      layout.semanticSiteOccurrences.get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (ConcreteElaboration.LocalOccurrence
      layout.plugRaw.regionCount layout.plugRaw.nodeCount))
    layout.semanticSiteOccurrences
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.frameRegion input.site)) _ _ _ index

def bodyInternalCarriers (layout : PlugLayout input) :
    List layout.internalWires.Carrier :=
  filterFin fun internal => decide
    ((input.pattern.val.diagram.wires
      (layout.internalWires.origin internal)).scope =
        input.binderSpine.bodyContainer)

def bodyInternalOriginalWires (layout : PlugLayout input) :
    List (Fin input.pattern.val.diagram.wireCount) :=
  layout.bodyInternalCarriers.map layout.internalWires.origin

theorem mem_bodyInternalOriginalWires (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    wire ∈ layout.bodyInternalOriginalWires ↔
      wire ∉ input.pattern.val.exposedWires ∧
        (input.pattern.val.diagram.wires wire).scope =
          input.binderSpine.bodyContainer := by
  constructor
  · intro hmember
    obtain ⟨internal, hsource, horigin⟩ := List.mem_map.mp hmember
    have hinternal : wire ∉ input.pattern.val.exposedWires := by
      rw [← horigin]
      exact (layout.internalWires_survives_iff _).1
        (layout.internalWires.origin_survives internal)
    have hscope : (input.pattern.val.diagram.wires
        (layout.internalWires.origin internal)).scope =
          input.binderSpine.bodyContainer :=
      decide_eq_true_iff.mp ((mem_filterFin internal).1 hsource)
    rw [horigin] at hscope
    exact ⟨hinternal, hscope⟩
  · rintro ⟨hinternal, hscope⟩
    let internal := layout.internalWires.index wire
      ((layout.internalWires_survives_iff wire).2 hinternal)
    apply List.mem_map.mpr
    refine ⟨internal, ?_, layout.internalWires.origin_index _ _⟩
    apply (mem_filterFin internal).2
    apply decide_eq_true_iff.mpr
    have horigin : layout.internalWires.origin internal = wire :=
      layout.internalWires.origin_index wire _
    rw [horigin]
    exact hscope

theorem bodyInternalOriginalWires_nodup (layout : PlugLayout input) :
    layout.bodyInternalOriginalWires.Nodup := by
  exact (filterFin_nodup _).map layout.internalWires.origin
    (fun left right hne heq => hne (layout.internalWires.origin_injective heq))

@[simp] theorem bodyInternalOriginalWires_length
    (layout : PlugLayout input) :
    layout.bodyInternalOriginalWires.length =
      layout.bodyInternalCarriers.length := by
  exact List.length_map layout.internalWires.origin

theorem bodyInternalOriginalWires_mem_exactScopeWires_iff
    (layout : PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    wire ∈ ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer ↔
      wire ∈ layout.bodyInternalOriginalWires := by
  have hbody := input.binderSpine.body_eq_terminal_of_nonempty hnonempty
  constructor
  · intro hlocal
    have hscope :=
      (ConcreteElaboration.mem_exactScopeWires _ _ wire).1 hlocal
    apply (layout.mem_bodyInternalOriginalWires wire).2
    refine ⟨?_, hscope⟩
    intro hexposed
    have hroot := input.pattern.property.boundary_is_root_scoped wire
      ((OpenConcreteDiagram.mem_exposedWires _ wire).1 hexposed)
    have himpossible : input.binderSpine.bodyContainer =
        input.pattern.val.diagram.root := hscope.symm.trans hroot
    rw [hbody] at himpossible
    exact input.binderSpine.proxy_ne_root (input.terminalProxy hnonempty)
      himpossible
  · intro hmember
    exact (ConcreteElaboration.mem_exactScopeWires _ _ wire).2
      ((layout.mem_bodyInternalOriginalWires wire).1 hmember).2

def bodyInternalExactEquiv
    (layout : PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    FiniteEquiv (Fin layout.bodyInternalCarriers.length)
      (Fin (ConcreteElaboration.exactScopeWires
        input.pattern.val.diagram input.binderSpine.bodyContainer).length) :=
  (FiniteEquiv.finCast layout.bodyInternalOriginalWires_length.symm).trans
    (FiniteEquiv.restrictLists
      (FiniteEquiv.refl (Fin input.pattern.val.diagram.wireCount))
      layout.bodyInternalOriginalWires
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer)
      layout.bodyInternalOriginalWires_nodup
      (ConcreteElaboration.exactScopeWires_nodup _ _)
      (fun wire => by
        simpa using
          (layout.bodyInternalOriginalWires_mem_exactScopeWires_iff
            hnonempty wire)))

theorem bodyInternalExactEquiv_spec
    (layout : PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin layout.bodyInternalCarriers.length) :
    (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
      input.binderSpine.bodyContainer).get
        (layout.bodyInternalExactEquiv hnonempty index) =
      layout.internalWires.origin
        (layout.bodyInternalCarriers.get index) := by
  have sourceNodup := layout.bodyInternalOriginalWires_nodup
  have targetNodup := ConcreteElaboration.exactScopeWires_nodup
    input.pattern.val.diagram input.binderSpine.bodyContainer
  have memIff : ∀ wire : Fin input.pattern.val.diagram.wireCount,
      (FiniteEquiv.refl (Fin input.pattern.val.diagram.wireCount)) wire ∈
          ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer ↔
        wire ∈ layout.bodyInternalOriginalWires := fun wire => by
    simpa using
      layout.bodyInternalOriginalWires_mem_exactScopeWires_iff
        hnonempty wire
  have hspec := FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin input.pattern.val.diagram.wireCount))
    layout.bodyInternalOriginalWires
    (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
      input.binderSpine.bodyContainer) sourceNodup targetNodup memIff
    (Fin.cast layout.bodyInternalOriginalWires_length.symm index)
  simpa [bodyInternalExactEquiv, bodyInternalOriginalWires,
    FiniteEquiv.finCast] using hspec

theorem bodyInternalOriginalWires_mem_hiddenWires_iff
    (layout : PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    wire ∈ input.pattern.val.hiddenWires ↔
      wire ∈ layout.bodyInternalOriginalWires := by
  rw [OpenConcreteDiagram.mem_hiddenWires,
    layout.mem_bodyInternalOriginalWires,
    input.binderSpine.body_eq_root_of_empty hzero]
  constructor
  · rintro ⟨hscope, hexposed⟩
    exact ⟨hexposed, hscope⟩
  · rintro ⟨hexposed, hscope⟩
    exact ⟨hscope, hexposed⟩

def bodyInternalHiddenEquiv
    (layout : PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0) :
    FiniteEquiv (Fin layout.bodyInternalCarriers.length)
      (Fin input.pattern.val.hiddenWires.length) :=
  (FiniteEquiv.finCast layout.bodyInternalOriginalWires_length.symm).trans
    (FiniteEquiv.restrictLists
      (FiniteEquiv.refl (Fin input.pattern.val.diagram.wireCount))
      layout.bodyInternalOriginalWires input.pattern.val.hiddenWires
      layout.bodyInternalOriginalWires_nodup
      input.pattern.val.hiddenWires_nodup
      (fun wire => by
        simpa using
          (layout.bodyInternalOriginalWires_mem_hiddenWires_iff hzero wire)))

theorem bodyInternalHiddenEquiv_spec
    (layout : PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin layout.bodyInternalCarriers.length) :
    input.pattern.val.hiddenWires.get
        (layout.bodyInternalHiddenEquiv hzero index) =
      layout.internalWires.origin
        (layout.bodyInternalCarriers.get index) := by
  have sourceNodup := layout.bodyInternalOriginalWires_nodup
  have targetNodup := input.pattern.val.hiddenWires_nodup
  have memIff : ∀ wire : Fin input.pattern.val.diagram.wireCount,
      (FiniteEquiv.refl (Fin input.pattern.val.diagram.wireCount)) wire ∈
          input.pattern.val.hiddenWires ↔
        wire ∈ layout.bodyInternalOriginalWires := fun wire => by
    simpa using layout.bodyInternalOriginalWires_mem_hiddenWires_iff
      hzero wire
  have hspec := FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin input.pattern.val.diagram.wireCount))
    layout.bodyInternalOriginalWires input.pattern.val.hiddenWires
    sourceNodup targetNodup memIff
    (Fin.cast layout.bodyInternalOriginalWires_length.symm index)
  simpa [bodyInternalHiddenEquiv, bodyInternalOriginalWires,
    FiniteEquiv.finCast] using hspec

def semanticSiteWires (layout : PlugLayout input) :
    List (Fin layout.plugRaw.wireCount) :=
  (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw input.site).map
      layout.frameWire ++
    layout.bodyInternalCarriers.map layout.internalWire

theorem semanticSiteWires_subset (layout : PlugLayout input) :
    ∀ wire, wire ∈ layout.semanticSiteWires →
      wire ∈ ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion input.site) := by
  intro wire hmem
  change wire ∈
    (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).map layout.frameWire ++
      layout.bodyInternalCarriers.map layout.internalWire at hmem
  have hparts := List.mem_append.mp hmem
  rw [ConcreteElaboration.mem_exactScopeWires]
  rcases hparts with hframe | hinternal
  · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hframe
    have hscope :=
      (ConcreteElaboration.mem_exactScopeWires _ _ _).1 hsource
    change (layout.plugWire (layout.frameWire source)).scope =
      layout.frameRegion input.site
    change (layout.plugWire (layout.quotientBlockWire source)).scope = _
    rw [plugWire_quotientBlockWire]
    simp only
    exact congrArg layout.frameRegion hscope
  · obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hinternal
    have hscope : (input.pattern.val.diagram.wires
        (layout.internalWires.origin source)).scope =
          input.binderSpine.bodyContainer := by
      exact decide_eq_true_iff.mp
        ((mem_filterFin source).1 hsource)
    change (layout.plugWire (layout.internalWire source)).scope =
      layout.frameRegion input.site
    change (layout.plugWire (layout.internalBlockWire source)).scope = _
    rw [plugWire_internalBlockWire]
    simp only [mapPatternWire, hscope, layout.bodyRegion_bodyContainer]

theorem semanticSiteWires_complete (layout : PlugLayout input) :
    ∀ wire, wire ∈ ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion input.site) →
      wire ∈ layout.semanticSiteWires := by
  intro wire hmem
  revert hmem
  simp only [semanticSiteWires]
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun frame => ?_)
    (fun internal => ?_) wire
  · intro hmem
    have hsource : frame ∈ ConcreteElaboration.exactScopeWires
        input.coalesceFrameRaw input.site := by
      apply (ConcreteElaboration.mem_exactScopeWires _ _ _).2
      rw [ConcreteElaboration.mem_exactScopeWires] at hmem
      change (layout.plugWire (layout.quotientBlockWire frame)).scope =
        layout.frameRegion input.site at hmem
      rw [plugWire_quotientBlockWire] at hmem
      exact layout.frameRegion_injective hmem
    apply List.mem_append_left
    exact List.mem_map_of_mem hsource
  · intro hmem
    have hsource : internal ∈ layout.bodyInternalCarriers := by
      change internal ∈ filterFin (fun internal => decide
        ((input.pattern.val.diagram.wires
          (layout.internalWires.origin internal)).scope =
            input.binderSpine.bodyContainer))
      apply (mem_filterFin internal).2
      apply decide_eq_true_iff.mpr
      rw [ConcreteElaboration.mem_exactScopeWires] at hmem
      change (layout.plugWire (layout.internalBlockWire internal)).scope =
        layout.frameRegion input.site at hmem
      rw [plugWire_internalBlockWire] at hmem
      simp only [mapPatternWire] at hmem
      let original := layout.internalWires.origin internal
      have hinternal : original ∉ input.pattern.val.exposedWires :=
        (layout.internalWires_survives_iff original).1
          (layout.internalWires.origin_survives internal)
      rcases patternInternalWire_scope_material_or_bodyContainer input original
          hinternal with hmaterial | hbody
      · rw [layout.bodyRegion_material _ hmaterial] at hmem
        exact False.elim
          (layout.frameRegion_ne_materialRegion input.site _ hmem.symm)
      · exact hbody
    apply List.mem_append_right
    exact List.mem_map_of_mem hsource

theorem semanticSiteWires_nodup (layout : PlugLayout input) :
    layout.semanticSiteWires.Nodup := by
  change ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
    input.site).map layout.frameWire ++
      layout.bodyInternalCarriers.map layout.internalWire).Nodup
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (ConcreteElaboration.exactScopeWires_nodup
      input.coalesceFrameRaw input.site).map layout.frameWire
        (fun left right hne heq => hne (layout.frameWire_injective heq))
  · exact (filterFin_nodup _).map layout.internalWire
      (fun left right hne heq => hne (layout.internalWire_injective heq))
  · intro frame hframe internal hinternal heq
    simp only [List.mem_map] at hframe hinternal
    rcases hframe with ⟨frameSource, _, rfl⟩
    rcases hinternal with ⟨internalSource, _, rfl⟩
    exact layout.frameWire_ne_internalWire frameSource internalSource heq

def siteWireEquiv (layout : PlugLayout input) :
    FiniteEquiv (Fin layout.semanticSiteWires.length)
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion input.site)).length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    layout.semanticSiteWires
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site))
    layout.semanticSiteWires_nodup
    (ConcreteElaboration.exactScopeWires_nodup _ _)
    (fun wire => ⟨layout.semanticSiteWires_complete wire,
      layout.semanticSiteWires_subset wire⟩)

theorem siteWireEquiv_spec (layout : PlugLayout input)
    (index : Fin layout.semanticSiteWires.length) :
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).get (layout.siteWireEquiv index) =
        layout.semanticSiteWires.get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    layout.semanticSiteWires
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)) _ _ _ index

@[simp] theorem semanticSiteWires_length (layout : PlugLayout input) :
    layout.semanticSiteWires.length =
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length + layout.bodyInternalCarriers.length := by
  change ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
    input.site).map layout.frameWire ++
      layout.bodyInternalCarriers.map layout.internalWire).length = _
  rw [List.length_append, List.length_map, List.length_map]
  rfl

/-- Local-wire equivalence for a nonempty proxy spine.  Its source is the
local block produced by intrinsic `spliceAt`: host locals followed by the
terminal pattern's locals. -/
def siteLocalWireEquivOfNonempty
    (layout : PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    FiniteEquiv
      (Fin ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length +
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).length))
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion input.site)).length) :=
  (extendWireEquiv
      (FiniteEquiv.refl (Fin
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length))
      (layout.bodyInternalExactEquiv hnonempty).symm).trans
    ((FiniteEquiv.finCast layout.semanticSiteWires_length.symm).trans
      layout.siteWireEquiv)

/-- Root-local variant for an empty proxy spine; the open pattern's hidden
root wires are precisely the material-local block. -/
def siteLocalWireEquivOfEmpty
    (layout : PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0) :
    FiniteEquiv
      (Fin ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length + input.pattern.val.hiddenWires.length))
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion input.site)).length) :=
  (extendWireEquiv
      (FiniteEquiv.refl (Fin
        (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length))
      (layout.bodyInternalHiddenEquiv hzero).symm).trans
    ((FiniteEquiv.finCast layout.semanticSiteWires_length.symm).trans
      layout.siteWireEquiv)

theorem siteLocalWireEquivOfNonempty_host_spec
    (layout : PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length) :
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).get
        (layout.siteLocalWireEquivOfNonempty hnonempty
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              input.pattern.val.diagram
              input.binderSpine.bodyContainer).length index)) =
      layout.frameWire
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).get index) := by
  rw [siteLocalWireEquivOfNonempty, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, layout.siteWireEquiv_spec]
  simp [FiniteEquiv.finCast, semanticSiteWires,
    extendWireEquiv]
  have hmap : index.val < ((ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).map layout.frameWire).length := by
    rw [List.length_map]
    exact index.isLt
  have happ : index.val <
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).map layout.frameWire ++
        layout.bodyInternalCarriers.map layout.internalWire).length := by
    rw [List.length_append]
    omega
  change ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).map layout.frameWire ++
      layout.bodyInternalCarriers.map layout.internalWire)[index.val]'happ =
    layout.frameWire
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site)[index.val]'index.isLt)
  rw [List.getElem_append_left hmap, List.getElem_map]
  rfl

theorem siteLocalWireEquivOfEmpty_host_spec
    (layout : PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length) :
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).get
        (layout.siteLocalWireEquivOfEmpty hzero
          (Fin.castAdd input.pattern.val.hiddenWires.length index)) =
      layout.frameWire
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).get index) := by
  rw [siteLocalWireEquivOfEmpty, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, layout.siteWireEquiv_spec]
  simp [FiniteEquiv.finCast, semanticSiteWires,
    extendWireEquiv]
  have hmap : index.val < ((ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).map layout.frameWire).length := by
    rw [List.length_map]
    exact index.isLt
  have happ : index.val <
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).map layout.frameWire ++
        layout.bodyInternalCarriers.map layout.internalWire).length := by
    rw [List.length_append]
    omega
  change ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).map layout.frameWire ++
      layout.bodyInternalCarriers.map layout.internalWire)[index.val]'happ =
    layout.frameWire
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site)[index.val]'index.isLt)
  rw [List.getElem_append_left hmap, List.getElem_map]
  rfl

theorem siteLocalWireEquivOfNonempty_pattern_spec
    (layout : PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length) :
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).get
        (layout.siteLocalWireEquivOfNonempty hnonempty
          (Fin.natAdd
            (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length index)) =
      layout.internalWire
        (layout.bodyInternalCarriers.get
          ((layout.bodyInternalExactEquiv hnonempty).symm index)) := by
  rw [siteLocalWireEquivOfNonempty, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, layout.siteWireEquiv_spec]
  simp [FiniteEquiv.finCast, semanticSiteWires,
    extendWireEquiv]
  let carrier := (layout.bodyInternalExactEquiv hnonempty).symm index
  let offset := (ConcreteElaboration.exactScopeWires
    input.coalesceFrameRaw input.site).length + carrier.val
  have happ : offset <
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).map layout.frameWire ++
        layout.bodyInternalCarriers.map layout.internalWire).length := by
    simp only [offset, List.length_append, List.length_map]
    exact Nat.add_lt_add_left carrier.isLt _
  change ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).map layout.frameWire ++
      layout.bodyInternalCarriers.map layout.internalWire)[offset]'happ =
    layout.internalWire (layout.bodyInternalCarriers[carrier.val]'carrier.isLt)
  have hright : ((ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).map layout.frameWire).length ≤
        offset := by
    rw [List.length_map]
    exact Nat.le_add_right _ _
  rw [List.getElem_append_right hright, List.getElem_map]
  have hleftVal : offset -
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).map layout.frameWire).length = carrier.val := by
    simp only [offset, List.length_map]
    exact Nat.add_sub_cancel_left _ _
  let leftIndex : Fin layout.bodyInternalCarriers.length :=
    ⟨offset - ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).map layout.frameWire).length,
      hleftVal ▸ carrier.isLt⟩
  change layout.internalWire
      (layout.bodyInternalCarriers.get leftIndex) =
    layout.internalWire (layout.bodyInternalCarriers.get carrier)
  apply congrArg layout.internalWire
  apply congrArg (List.get layout.bodyInternalCarriers)
  exact Fin.ext hleftVal

theorem siteLocalWireEquivOfEmpty_pattern_spec
    (layout : PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin input.pattern.val.hiddenWires.length) :
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).get
        (layout.siteLocalWireEquivOfEmpty hzero
          (Fin.natAdd
            (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length index)) =
      layout.internalWire
        (layout.bodyInternalCarriers.get
          ((layout.bodyInternalHiddenEquiv hzero).symm index)) := by
  rw [siteLocalWireEquivOfEmpty, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, layout.siteWireEquiv_spec]
  simp [FiniteEquiv.finCast, semanticSiteWires,
    extendWireEquiv]
  let carrier := (layout.bodyInternalHiddenEquiv hzero).symm index
  let offset := (ConcreteElaboration.exactScopeWires
    input.coalesceFrameRaw input.site).length + carrier.val
  have happ : offset <
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).map layout.frameWire ++
        layout.bodyInternalCarriers.map layout.internalWire).length := by
    simp only [offset, List.length_append, List.length_map]
    exact Nat.add_lt_add_left carrier.isLt _
  change ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).map layout.frameWire ++
      layout.bodyInternalCarriers.map layout.internalWire)[offset]'happ =
    layout.internalWire (layout.bodyInternalCarriers[carrier.val]'carrier.isLt)
  have hright : ((ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).map layout.frameWire).length ≤
        offset := by
    rw [List.length_map]
    exact Nat.le_add_right _ _
  rw [List.getElem_append_right hright, List.getElem_map]
  have hleftVal : offset -
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).map layout.frameWire).length = carrier.val := by
    simp only [offset, List.length_map]
    exact Nat.add_sub_cancel_left _ _
  let leftIndex : Fin layout.bodyInternalCarriers.length :=
    ⟨offset - ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
      input.site).map layout.frameWire).length,
      hleftVal ▸ carrier.isLt⟩
  change layout.internalWire
      (layout.bodyInternalCarriers.get leftIndex) =
    layout.internalWire (layout.bodyInternalCarriers.get carrier)
  apply congrArg layout.internalWire
  apply congrArg (List.get layout.bodyInternalCarriers)
  exact Fin.ext hleftVal

theorem material_climb_body_and_plug_site (layout : PlugLayout input) :
    ∀ (fuel : Nat) (region : Fin input.pattern.val.diagram.regionCount),
      input.binderSpine.IsMaterialRegion region →
      input.pattern.val.diagram.climb fuel region =
        some input.pattern.val.diagram.root →
      ∃ steps : Nat,
        input.pattern.val.diagram.climb steps region =
            some input.binderSpine.bodyContainer ∧
          layout.plugRaw.climb steps (layout.bodyRegion region) =
            some (layout.frameRegion input.site) := by
  intro fuel
  induction fuel with
  | zero =>
      intro region hmaterial hclimb
      have hroot : region = input.pattern.val.diagram.root :=
        Option.some.inj hclimb
      exact False.elim (hmaterial.1 hroot)
  | succ fuel ih =>
      intro region hmaterial hclimb
      cases hparent : (input.pattern.val.diagram.regions region).parent? with
      | none => simp [ConcreteDiagram.climb, hparent] at hclimb
      | some parent =>
          have htail : input.pattern.val.diagram.climb fuel parent =
              some input.pattern.val.diagram.root := by
            simpa [ConcreteDiagram.climb, hparent] using hclimb
          by_cases hparentMaterial :
              input.binderSpine.IsMaterialRegion parent
          · obtain ⟨steps, horiginal, hplug⟩ :=
              ih parent hparentMaterial htail
            refine ⟨1 + steps, ?_, ?_⟩
            · exact ConcreteElaboration.climb_add (by
                simp [ConcreteDiagram.climb, hparent]) horiginal
            · have hstep : layout.plugRaw.climb 1
                  (layout.bodyRegion region) =
                  some (layout.bodyRegion parent) := by
                simp only [ConcreteDiagram.climb]
                rw [layout.bodyRegion_parent_exact
                  region parent hmaterial hparent]
                rfl
              exact ConcreteElaboration.climb_add hstep hplug
          · have hbody := nonmaterial_parent_eq_bodyContainer (input := input)
              region parent hmaterial hparent hparentMaterial
            refine ⟨1, ?_, ?_⟩
            · simpa [ConcreteDiagram.climb, hparent] using congrArg some hbody
            · simp only [ConcreteDiagram.climb]
              rw [layout.bodyRegion_parent_exact
                region parent hmaterial hparent]
              exact congrArg some
                (layout.bodyRegion_nonmaterial parent hparentMaterial)

theorem material_of_climb_lt_bodyContainer (input : Input signature) :
    ∀ (steps : Nat)
      (region current : Fin input.pattern.val.diagram.regionCount)
      (position : Nat),
      input.binderSpine.IsMaterialRegion region →
      input.pattern.val.diagram.climb steps region =
        some input.binderSpine.bodyContainer →
      position < steps →
      input.pattern.val.diagram.climb position region = some current →
      input.binderSpine.IsMaterialRegion current := by
  intro steps
  induction steps with
  | zero =>
      intro region current position _ _ hlt _
      omega
  | succ steps ih =>
      intro region current position hmaterial hbody hlt hposition
      cases position with
      | zero =>
          have heq : region = current := Option.some.inj hposition
          simpa only [← heq] using hmaterial
      | succ position =>
          cases hparent : (input.pattern.val.diagram.regions region).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at hbody
          | some parent =>
              have htail : input.pattern.val.diagram.climb steps parent =
                  some input.binderSpine.bodyContainer := by
                simpa [ConcreteDiagram.climb, hparent] using hbody
              have hpositionTail :
                  input.pattern.val.diagram.climb position parent =
                    some current := by
                simpa [ConcreteDiagram.climb, hparent] using hposition
              have hparentMaterial :
                  input.binderSpine.IsMaterialRegion parent := by
                by_cases hcandidate :
                    input.binderSpine.IsMaterialRegion parent
                · exact hcandidate
                · have hparentBody := nonmaterial_parent_eq_bodyContainer
                    (input := input) region parent hmaterial hparent hcandidate
                  obtain ⟨rootSteps, hbodyRoot⟩ :=
                    input.pattern.property.diagram_well_formed
                      |>.all_regions_reach_root input.binderSpine.bodyContainer
                  have hcycleRoot := ConcreteElaboration.climb_add
                    htail hbodyRoot
                  rw [hparentBody] at hcycleRoot
                  have hunique :=
                    ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique
                      input.pattern.val.diagram
                      input.pattern.property.diagram_well_formed.root_is_sheet
                      hcycleRoot hbodyRoot
                  omega
              exact ih parent current position hparentMaterial htail
                (by omega) hpositionTail

theorem material_climb_steps_le_count (layout : PlugLayout input)
    {steps : Nat} {region : Fin input.pattern.val.diagram.regionCount}
    (hmaterial : input.binderSpine.IsMaterialRegion region)
    (hclimb : input.pattern.val.diagram.climb steps region =
      some input.binderSpine.bodyContainer) :
    steps ≤ layout.materialRegions.count := by
  let pathIsSome (position : Fin steps) :
      (input.pattern.val.diagram.climb position.val region).isSome = true :=
    Option.isSome_iff_exists.mpr
      (splice_climb_prefix_exists (Nat.le_of_lt position.isLt) hclimb)
  let path (position : Fin steps) :
      Fin input.pattern.val.diagram.regionCount :=
    (input.pattern.val.diagram.climb position.val region).get
      (pathIsSome position)
  have path_spec (position : Fin steps) :
      input.pattern.val.diagram.climb position.val region =
        some (path position) :=
    (Option.some_get (pathIsSome position)).symm
  have path_material (position : Fin steps) :
      input.binderSpine.IsMaterialRegion (path position) :=
    material_of_climb_lt_bodyContainer input steps region (path position)
      position.val hmaterial hclimb position.isLt (path_spec position)
  let pathIndex (position : Fin steps) :
      layout.materialRegions.Carrier :=
    layout.materialIndex (path position) (path_material position)
  have pathIndex_injective : Function.Injective pathIndex := by
    intro first second heq
    have hpaths : path first = path second := by
      have horigins := congrArg layout.materialRegions.origin heq
      simpa only [pathIndex, materialIndex,
        SurvivorDomain.origin_index] using horigins
    obtain ⟨bodyRootSteps, hbodyRoot⟩ :=
      input.pattern.property.diagram_well_formed
        |>.all_regions_reach_root input.binderSpine.bodyContainer
    have hfirstSuffix := splice_climb_cancel_prefix
      (Nat.le_of_lt first.isLt) (path_spec first) hclimb
    have hsecondSuffix := splice_climb_cancel_prefix
      (Nat.le_of_lt second.isLt) (path_spec second) hclimb
    have hfirstRoot := ConcreteElaboration.climb_add hfirstSuffix hbodyRoot
    have hsecondRoot := ConcreteElaboration.climb_add hsecondSuffix hbodyRoot
    rw [hpaths] at hfirstRoot
    have hremaining :=
      ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique
        input.pattern.val.diagram
        input.pattern.property.diagram_well_formed.root_is_sheet
        hfirstRoot hsecondRoot
    apply Fin.ext
    omega
  exact fin_card_le_of_injective pathIndex pathIndex_injective

theorem frame_climb (layout : PlugLayout input) :
    ∀ (steps : Nat) (start finish : Fin input.frame.val.regionCount),
      input.frame.val.climb steps start = some finish →
      layout.plugRaw.climb steps (layout.frameRegion start) =
        some (layout.frameRegion finish) := by
  intro steps
  induction steps with
  | zero =>
      intro start finish hclimb
      have heq : start = finish := Option.some.inj hclimb
      subst finish
      rfl
  | succ steps ih =>
      intro start finish hclimb
      cases hregion : input.frame.val.regions start with
      | sheet =>
          simp [ConcreteDiagram.climb, hregion, CRegion.parent?] at hclimb
      | cut parent =>
          have htail : input.frame.val.climb steps parent = some finish := by
            simpa [ConcreteDiagram.climb, hregion] using hclimb
          simp only [ConcreteDiagram.climb, plugRaw,
            plugRegion_frameRegion, hregion, mapFrameRegion, CRegion.parent?]
          exact ih parent finish htail
      | bubble parent arity =>
          have htail : input.frame.val.climb steps parent = some finish := by
            simpa [ConcreteDiagram.climb, hregion] using hclimb
          simp only [ConcreteDiagram.climb, plugRaw,
            plugRegion_frameRegion, hregion, mapFrameRegion, CRegion.parent?]
          exact ih parent finish htail

theorem frame_climb_iff (layout : PlugLayout input)
    (steps : Nat) (start finish : Fin input.frame.val.regionCount) :
    layout.plugRaw.climb steps (layout.frameRegion start) =
        some (layout.frameRegion finish) ↔
      input.frame.val.climb steps start = some finish := by
  constructor
  · intro hclimb
    induction steps generalizing start with
    | zero =>
        have heq : layout.frameRegion start = layout.frameRegion finish :=
          Option.some.inj hclimb
        simpa [ConcreteDiagram.climb, layout.frameRegion_injective heq]
    | succ steps ih =>
        cases hregion : input.frame.val.regions start with
        | sheet =>
            simp [ConcreteDiagram.climb, plugRaw, plugRegion_frameRegion,
              hregion, mapFrameRegion, CRegion.parent?] at hclimb
        | cut parent =>
            have htail : layout.plugRaw.climb steps
                (layout.frameRegion parent) =
                  some (layout.frameRegion finish) := by
              simpa [ConcreteDiagram.climb, plugRaw, plugRegion_frameRegion,
                hregion, mapFrameRegion, CRegion.parent?] using hclimb
            simpa [ConcreteDiagram.climb, hregion] using ih parent htail
        | bubble parent arity =>
            have htail : layout.plugRaw.climb steps
                (layout.frameRegion parent) =
                  some (layout.frameRegion finish) := by
              simpa [ConcreteDiagram.climb, plugRaw, plugRegion_frameRegion,
                hregion, mapFrameRegion, CRegion.parent?] using hclimb
            simpa [ConcreteDiagram.climb, hregion] using ih parent htail
  · exact layout.frame_climb steps start finish

theorem checked_encloses_antisymm
    {diagram : ConcreteDiagram} (hroot : diagram.RootIsSheet)
    (hall : diagram.AllRegionsReachRoot)
    {left right : Fin diagram.regionCount}
    (hleft : diagram.Encloses left right)
    (hright : diagram.Encloses right left) : left = right := by
  obtain ⟨leftSteps, hleft⟩ := hleft
  obtain ⟨rightSteps, hright⟩ := hright
  obtain ⟨rootSteps, htoRoot⟩ := hall right
  have hcycle : diagram.climb (leftSteps.val + rightSteps.val) right =
      some right := ConcreteElaboration.climb_add hleft hright
  have hcycleRoot := ConcreteElaboration.climb_add hcycle htoRoot
  have hlength :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique diagram
      hroot hcycleRoot htoRoot
  have hzero : leftSteps.val = 0 := by omega
  rw [hzero] at hleft
  simpa [ConcreteDiagram.climb] using hleft.symm

theorem plugRaw_all_regions_reach_root (layout : PlugLayout input) :
    layout.plugRaw.AllRegionsReachRoot := by
  intro region
  refine Fin.addCases (m := input.frame.val.regionCount)
    (n := layout.materialRegions.count)
    (fun frame => ?_) (fun material => ?_) region
  · obtain ⟨steps, hframe⟩ :=
      input.frame.property.all_regions_reach_root frame
    refine ⟨⟨steps.val, by
      simp only [plugRaw, regionCount]
      omega⟩, ?_⟩
    exact layout.frame_climb steps.val frame input.frame.val.root hframe
  · let original := layout.materialRegions.origin material
    have hmaterial : input.binderSpine.IsMaterialRegion original :=
      (layout.materialRegions_survives_iff original).1
        (layout.materialRegions.origin_survives material)
    obtain ⟨patternSteps, hpatternRoot⟩ :=
      input.pattern.property.diagram_well_formed.all_regions_reach_root original
    obtain ⟨materialSteps, hmaterialBody, hmaterialSite⟩ :=
      layout.material_climb_body_and_plug_site patternSteps.val original
        hmaterial hpatternRoot
    have hmaterialBound :=
      layout.material_climb_steps_le_count hmaterial hmaterialBody
    obtain ⟨frameSteps, hsiteRoot⟩ :=
      input.frame.property.all_regions_reach_root input.site
    have hframeRoot := layout.frame_climb frameSteps.val input.site
      input.frame.val.root hsiteRoot
    have hplugRoot := ConcreteElaboration.climb_add hmaterialSite hframeRoot
    refine ⟨⟨materialSteps + frameSteps.val, by
      simp only [plugRaw, regionCount]
      omega⟩, ?_⟩
    simpa only [original, layout.bodyRegion_origin material] using hplugRoot

theorem plugRaw_root_is_sheet (layout : PlugLayout input) :
    layout.plugRaw.RootIsSheet := by
  unfold ConcreteDiagram.RootIsSheet
  change layout.plugRegion (layout.frameRegion input.frame.val.root) = .sheet
  rw [layout.plugRegion_frameRegion]
  rw [input.frame.property.root_is_sheet]
  rfl

theorem plugRaw_only_root_is_sheet (layout : PlugLayout input) :
    layout.plugRaw.OnlyRootIsSheet := by
  intro region
  refine Fin.addCases (m := input.frame.val.regionCount)
    (n := layout.materialRegions.count)
    (fun frame => ?_) (fun material => ?_) region
  · intro hsheet
    simp only [plugRaw] at hsheet
    change layout.plugRegion (layout.frameRegion frame) = .sheet at hsheet
    rw [layout.plugRegion_frameRegion frame] at hsheet
    have hframeSheet : input.frame.val.regions frame = .sheet := by
      cases hregion : input.frame.val.regions frame with
      | sheet => rfl
      | cut => simp [hregion, mapFrameRegion] at hsheet
      | bubble => simp [hregion, mapFrameRegion] at hsheet
    have hroot := input.frame.property.only_root_is_sheet frame hframeSheet
    subst frame
    rfl
  · intro hsheet
    simp only [plugRaw] at hsheet
    change layout.plugRegion (layout.materialRegion material) = .sheet at hsheet
    rw [layout.plugRegion_materialRegion material] at hsheet
    have himpossible : layout.mapPatternRegion
        (input.pattern.val.diagram.regions
          (layout.materialRegions.origin material)) ≠ .sheet := by
      cases input.pattern.val.diagram.regions
          (layout.materialRegions.origin material) <;>
        simp [mapPatternRegion]
    exact False.elim (himpossible hsheet)

theorem plugRaw_encloses_trans (layout : PlugLayout input)
    {ancestor middle descendant : Fin layout.plugRaw.regionCount}
    (hfirst : layout.plugRaw.Encloses ancestor middle)
    (hsecond : layout.plugRaw.Encloses middle descendant) :
    layout.plugRaw.Encloses ancestor descendant := by
  obtain ⟨first, hfirst⟩ := hfirst
  obtain ⟨second, hsecond⟩ := hsecond
  obtain ⟨rootSteps, hroot⟩ :=
    layout.plugRaw_all_regions_reach_root ancestor
  have hcomposed := ConcreteElaboration.climb_add hsecond hfirst
  have htoRoot := ConcreteElaboration.climb_add hcomposed hroot
  have hbound :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_le_regionCount
      layout.plugRaw layout.plugRaw_root_is_sheet
      layout.plugRaw_all_regions_reach_root htoRoot
  exact ⟨⟨second.val + first.val, by omega⟩, hcomposed⟩

theorem frame_encloses (layout : PlugLayout input)
    {ancestor descendant : Fin input.frame.val.regionCount}
    (hencloses : input.frame.val.Encloses ancestor descendant) :
    layout.plugRaw.Encloses (layout.frameRegion ancestor)
      (layout.frameRegion descendant) := by
  obtain ⟨steps, hsteps⟩ := hencloses
  refine ⟨⟨steps.val, by
    simp only [plugRaw, regionCount]
    omega⟩, layout.frame_climb steps.val descendant ancestor hsteps⟩

theorem frame_encloses_iff (layout : PlugLayout input)
    (ancestor descendant : Fin input.frame.val.regionCount) :
    layout.plugRaw.Encloses (layout.frameRegion ancestor)
        (layout.frameRegion descendant) ↔
      input.frame.val.Encloses ancestor descendant := by
  constructor
  · rintro ⟨steps, hsteps⟩
    have hframe :=
      (layout.frame_climb_iff steps.val descendant ancestor).1 hsteps
    obtain ⟨rootSteps, hroot⟩ :=
      input.frame.property.all_regions_reach_root ancestor
    have htoRoot := ConcreteElaboration.climb_add hframe hroot
    have hbound :=
      ConcreteElaboration.ParentTraversal.climb_to_root_steps_le_regionCount
        input.frame.val input.frame.property.root_is_sheet
        input.frame.property.all_regions_reach_root htoRoot
    exact ⟨⟨steps.val, by omega⟩, hframe⟩
  · exact layout.frame_encloses

theorem frameWire_visible_at_region_iff (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (wire : Fin input.coalesceFrameRaw.wireCount) :
    layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.frameWire wire)).scope
        (layout.frameRegion region) ↔
      input.coalesceFrameRaw.Encloses
        (input.coalesceFrameRaw.wires wire).scope region := by
  change layout.plugRaw.Encloses
      (layout.plugWire (layout.quotientBlockWire wire)).scope
      (layout.frameRegion region) ↔ _
  rw [plugWire_quotientBlockWire]
  change layout.plugRaw.Encloses
      (layout.frameRegion (input.coalescedScope wire))
      (layout.frameRegion region) ↔ _
  rw [layout.frame_encloses_iff,
    input.coalesceFrameRaw_encloses_iff]
  rfl

theorem frameWire_mem_context_iff (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.frameRegion region))
    (wire : Fin input.coalesceFrameRaw.wireCount) :
    layout.frameWire wire ∈ targetContext ↔ wire ∈ sourceContext := by
  calc
    layout.frameWire wire ∈ targetContext ↔
        layout.plugRaw.Encloses
          (layout.plugRaw.wires (layout.frameWire wire)).scope
          (layout.frameRegion region) :=
      targetExact.mem_iff (layout.frameWire wire)
    _ ↔ input.coalesceFrameRaw.Encloses
          (input.coalesceFrameRaw.wires wire).scope region :=
      layout.frameWire_visible_at_region_iff region wire
    _ ↔ wire ∈ sourceContext := (sourceExact.mem_iff wire).symm

theorem site_encloses_bodyRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    layout.plugRaw.Encloses (layout.frameRegion input.site)
      (layout.bodyRegion region) := by
  by_cases hmaterial : input.binderSpine.IsMaterialRegion region
  · obtain ⟨patternSteps, hpatternRoot⟩ :=
      input.pattern.property.diagram_well_formed.all_regions_reach_root region
    obtain ⟨steps, horiginal, hplug⟩ :=
      layout.material_climb_body_and_plug_site patternSteps.val region
        hmaterial hpatternRoot
    have hbound := layout.material_climb_steps_le_count hmaterial horiginal
    refine ⟨⟨steps, by
      simp only [plugRaw, regionCount]
      have := input.frame.val.root.isLt
      omega⟩, hplug⟩
  · rw [layout.bodyRegion_nonmaterial region hmaterial]
    exact ConcreteDiagram.Encloses.refl _ _

theorem frameWire_inherited_mem_iff
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (wire : input.wireQuotient.Carrier) :
    layout.frameWire wire ∈ outputLeaf.inheritedWires ↔
      wire ∈ hostLeaf.inheritedWires := by
  constructor
  · intro hmember
    have houtput :=
      (outputLeaf.inherited_mem_iff outputWitness
        (layout.frameWire wire)).1 hmember
    have hscope :
        (layout.plugRaw.wires (layout.frameWire wire)).scope =
          layout.frameRegion (input.coalescedScope wire) := by
      change (layout.plugWire (layout.quotientBlockWire wire)).scope = _
      rw [plugWire_quotientBlockWire]
    apply (hostLeaf.inherited_mem_iff hostWitness wire).2
    refine ⟨?_, ?_⟩
    · apply (input.coalesceFrameRaw_encloses_iff _ _).2
      apply (layout.frame_encloses_iff _ _).1
      simpa [hscope] using houtput.1
    · intro hlocal
      apply houtput.2
      calc
        (layout.plugRaw.wires (layout.frameWire wire)).scope =
            layout.frameRegion (input.coalescedScope wire) := hscope
        _ = layout.frameRegion input.site :=
          congrArg layout.frameRegion (by simpa using hlocal)
  · intro hmember
    have hhost := (hostLeaf.inherited_mem_iff hostWitness wire).1 hmember
    apply (outputLeaf.inherited_mem_iff outputWitness
      (layout.frameWire wire)).2
    have hscope :
        (layout.plugRaw.wires (layout.frameWire wire)).scope =
          layout.frameRegion (input.coalescedScope wire) := by
      change (layout.plugWire (layout.quotientBlockWire wire)).scope = _
      rw [plugWire_quotientBlockWire]
    refine ⟨?_, ?_⟩
    · have hframe : input.frame.val.Encloses
          (input.coalescedScope wire) input.site :=
        (input.coalesceFrameRaw_encloses_iff _ _).1 (by
          simpa using hhost.1)
      have houtput := (layout.frame_encloses_iff _ _).2 hframe
      simpa [hscope] using houtput
    · intro heq
      apply hhost.2
      have hmapped : layout.frameRegion (input.coalescedScope wire) =
          layout.frameRegion input.site := hscope.symm.trans heq
      simpa using layout.frameRegion_injective hmapped

theorem internalWire_not_in_inherited
    (layout : PlugLayout input)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (wire : layout.internalWires.Carrier) :
    layout.internalWire wire ∉ outputLeaf.inheritedWires := by
  intro hinherited
  have hstrict :=
    (outputLeaf.inherited_mem_iff outputWitness
      (layout.internalWire wire)).1 hinherited
  let original := layout.internalWires.origin wire
  have hinternal : original ∉ input.pattern.val.exposedWires :=
    (layout.internalWires_survives_iff original).1
      (layout.internalWires.origin_survives wire)
  rcases patternInternalWire_scope_material_or_bodyContainer input original
      hinternal with hmaterial | hbody
  · have hscope :
        (layout.plugRaw.wires (layout.internalWire wire)).scope =
          layout.bodyRegion
            (input.pattern.val.diagram.wires original).scope := by
      change (layout.plugWire (layout.internalBlockWire wire)).scope = _
      rw [plugWire_internalBlockWire]
      rfl
    have hsiteEncloses := layout.site_encloses_bodyRegion
      (input.pattern.val.diagram.wires original).scope
    have hmaterialRegion : input.binderSpine.IsMaterialRegion
        (input.pattern.val.diagram.wires original).scope := hmaterial
    have hreverse : layout.plugRaw.Encloses
        (layout.bodyRegion (input.pattern.val.diagram.wires original).scope)
        (layout.frameRegion input.site) := by
      simpa [hscope] using hstrict.1
    have heq := checked_encloses_antisymm
      layout.plugRaw_root_is_sheet layout.plugRaw_all_regions_reach_root
      hreverse hsiteEncloses
    rw [layout.bodyRegion_material _ hmaterialRegion] at heq
    exact layout.frameRegion_ne_materialRegion input.site _ heq.symm
  · apply hstrict.2
    change (layout.plugWire (layout.internalBlockWire wire)).scope = _
    rw [plugWire_internalBlockWire]
    simp only [mapPatternWire]
    rw [show (input.pattern.val.diagram.wires
      (layout.internalWires.origin wire)).scope =
        input.binderSpine.bodyContainer by simpa [original] using hbody,
      layout.bodyRegion_bodyContainer]

def semanticInheritedWires
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness) : List (Fin layout.plugRaw.wireCount) :=
  hostLeaf.inheritedWires.map layout.frameWire

theorem semanticInheritedWires_subset
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    ∀ wire,
      wire ∈ layout.semanticInheritedWires hostWitness hostLeaf →
        wire ∈ outputLeaf.inheritedWires := by
  intro wire hmember
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmember
  exact (layout.frameWire_inherited_mem_iff hostWitness hostLeaf
    outputWitness outputLeaf source).2 hsource

theorem semanticInheritedWires_complete
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    ∀ wire, wire ∈ outputLeaf.inheritedWires →
      wire ∈ layout.semanticInheritedWires hostWitness hostLeaf := by
  intro wire
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun frame => ?_)
    (fun internal => ?_) wire
  · intro hmember
    apply List.mem_map_of_mem
    exact (layout.frameWire_inherited_mem_iff hostWitness hostLeaf
      outputWitness outputLeaf frame).1 hmember
  · intro hmember
    exact False.elim
      (layout.internalWire_not_in_inherited outputWitness outputLeaf internal
        hmember)

theorem semanticInheritedWires_nodup
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness) :
    (layout.semanticInheritedWires hostWitness hostLeaf).Nodup := by
  have hn := hostLeaf.wiresExact.nodup
  rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at hn
  exact hn.1.map layout.frameWire
    (fun left right hne heq => hne (layout.frameWire_injective heq))

@[simp] theorem semanticInheritedWires_length
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness) :
    (layout.semanticInheritedWires hostWitness hostLeaf).length =
      hostLeaf.inheritedWires.length := by
  exact List.length_map layout.frameWire

def inheritedWireEquiv
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    FiniteEquiv (Fin hostLeaf.inheritedWires.length)
      (Fin outputLeaf.inheritedWires.length) :=
  (FiniteEquiv.finCast
      (layout.semanticInheritedWires_length hostWitness hostLeaf).symm).trans
    (FiniteEquiv.restrictLists
      (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
      (layout.semanticInheritedWires hostWitness hostLeaf)
      outputLeaf.inheritedWires
      (layout.semanticInheritedWires_nodup hostWitness hostLeaf)
      (by
        have hn := outputLeaf.wiresExact.nodup
        rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at hn
        exact hn.1)
      (fun wire => ⟨
        layout.semanticInheritedWires_complete hostWitness hostLeaf
          outputWitness outputLeaf wire,
        layout.semanticInheritedWires_subset hostWitness hostLeaf
          outputWitness outputLeaf wire⟩))

theorem inheritedWireEquiv_spec
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (index : Fin hostLeaf.inheritedWires.length) :
    outputLeaf.inheritedWires.get
        (layout.inheritedWireEquiv hostWitness hostLeaf outputWitness
          outputLeaf index) =
      layout.frameWire (hostLeaf.inheritedWires.get index) := by
  have sourceNodup :=
    layout.semanticInheritedWires_nodup hostWitness hostLeaf
  have targetNodup : outputLeaf.inheritedWires.Nodup := by
    have hn := outputLeaf.wiresExact.nodup
    rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at hn
    exact hn.1
  have memIff : ∀ wire : Fin layout.plugRaw.wireCount,
      (FiniteEquiv.refl (Fin layout.plugRaw.wireCount)) wire ∈
          outputLeaf.inheritedWires ↔
        wire ∈ layout.semanticInheritedWires hostWitness hostLeaf :=
    fun wire => ⟨
      layout.semanticInheritedWires_complete hostWitness hostLeaf
        outputWitness outputLeaf wire,
      layout.semanticInheritedWires_subset hostWitness hostLeaf
        outputWitness outputLeaf wire⟩
  have hspec := FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    (layout.semanticInheritedWires hostWitness hostLeaf)
    outputLeaf.inheritedWires sourceNodup targetNodup memIff
      (Fin.cast
        (layout.semanticInheritedWires_length hostWitness hostLeaf).symm index)
  simpa [inheritedWireEquiv, semanticInheritedWires,
    FiniteEquiv.finCast] using hspec

end PlugLayout

end VisualProof.Diagram.Splice.Input
