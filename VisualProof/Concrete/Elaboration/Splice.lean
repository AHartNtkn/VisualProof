import VisualProof.Concrete.Elaboration.Compiled
import VisualProof.Concrete.Elaboration.SpliceWireLayout

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open Elaboration

/-!
Concrete splice refinement is proved over the symbolic compiler tree.  This
module owns only splice-specific identity maps and the graft transformation;
lexical positions are introduced by `CompiledRegion.erase`.
-/

namespace Splice.Input.PlugLayout

/-- A frame endpoint remains on the image of its source wire. -/
theorem endpointOccurs_frame (layout : PlugLayout input)
    {wire : Fin input.frame.val.wireCount}
    {endpoint : CEndpoint input.frame.val.nodeCount}
    (occurs : input.frame.val.EndpointOccurs wire endpoint) :
    layout.plugRaw.EndpointOccurs (layout.frameWireMap wire)
      (layout.mapFrameEndpoint endpoint) := by
  change layout.mapFrameEndpoint endpoint ∈
    (layout.plugRaw.wires (layout.frameWireMap wire)).endpoints
  rw [show layout.frameWireMap wire =
      layout.frameWire (input.quotientWire wire) from rfl,
    layout.plugRaw_wires_frame]
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨endpoint,
    input.endpointOccurs_quotient wire endpoint occurs, rfl⟩

private theorem boundaryWires_contains_exposed
    (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    input.pattern.val.exposedWires.get external ∈
      layout.boundaryWires (layout.exposedAttachment external) := by
  unfold PlugLayout.boundaryWires
  apply List.mem_map.mpr
  refine ⟨external, ?_, rfl⟩
  simp

/-- A pattern endpoint remains on the image of its source wire.  Boundary
wire aliases are routed through the concrete attachment quotient; internal
wires use their dense material allocation. -/
theorem endpointOccurs_pattern (layout : PlugLayout input)
    {wire : Fin input.pattern.val.diagram.wireCount}
    {endpoint : CEndpoint input.pattern.val.diagram.nodeCount}
    (occurs : input.pattern.val.diagram.EndpointOccurs wire endpoint) :
    layout.plugRaw.EndpointOccurs (layout.patternWireMap wire)
      (layout.mapPatternEndpoint endpoint) := by
  by_cases exposed : wire ∈ input.pattern.val.exposedWires
  · let found := (indexOf? input.pattern.val.exposedWires wire).get
      ((indexOf?_isSome_iff).2 exposed)
    have foundEq : input.pattern.val.exposedWires.get found = wire := by
      exact indexOf?_sound (Option.some_get
        ((indexOf?_isSome_iff).2 exposed)).symm
    rw [← foundEq, layout.patternWireMap_exposed]
    change layout.mapPatternEndpoint endpoint ∈
      (layout.plugRaw.wires
        (layout.frameWire (layout.exposedAttachment found))).endpoints
    rw [layout.plugRaw_wires_frame]
    apply List.mem_append_right
    unfold PlugLayout.boundaryEndpoints
    apply List.mem_map.mpr
    refine ⟨endpoint, ?_, rfl⟩
    rw [List.mem_flatMap]
    refine ⟨input.pattern.val.exposedWires.get found,
      layout.boundaryWires_contains_exposed found, ?_⟩
    rw [foundEq]
    exact occurs
  · let internal := layout.internalWires.index wire (by
      rw [layout.internalWires_exact]
      exact decide_eq_true exposed)
    have originEq : layout.internalWires.origin internal = wire :=
      layout.internalWires.origin_index wire (by
        rw [layout.internalWires_exact]
        exact decide_eq_true exposed)
    rw [← originEq, layout.patternWireMap_internal,
      show layout.plugRaw.EndpointOccurs
          (layout.internalWire internal) (layout.mapPatternEndpoint endpoint) ↔
        layout.mapPatternEndpoint endpoint ∈
          (layout.plugRaw.wires (layout.internalWire internal)).endpoints
        from Iff.rfl,
      layout.plugRaw_wires_internal]
    change layout.mapPatternEndpoint endpoint ∈
      (input.pattern.val.diagram.wires
        (layout.internalWires.origin internal)).endpoints.map
          layout.mapPatternEndpoint
    apply List.mem_map.mpr
    refine ⟨endpoint, ?_, rfl⟩
    rw [originEq]
    exact occurs

/-! Source-derived symbolic graft. -/

mutual
  /-- Map the retained frame tree, inserting the pattern terminal's two
  canonical blocks exactly at the selected site. -/
  def graftFrameRegion (layout : PlugLayout input)
      (material : CompiledRegion input.pattern.val.diagram) :
      CompiledRegion input.frame.val → CompiledRegion layout.plugRaw
    | .mk origin nodes children =>
        if origin = input.site then
          .mk (layout.frameRegion origin)
            ((layout.graftFrameItems material nodes).append
              (layout.graftPatternItems material.nodeItems))
            ((layout.graftFrameItems material children).append
              (layout.graftPatternItems material.childItems))
        else
          .mk (layout.frameRegion origin)
            (layout.graftFrameItems material nodes)
            (layout.graftFrameItems material children)

  def graftFrameItem (layout : PlugLayout input)
      (material : CompiledRegion input.pattern.val.diagram) :
      CompiledItem input.frame.val → CompiledItem layout.plugRaw
    | .atom origin binder arity ports =>
        .atom (layout.frameNode origin) (layout.frameRegion binder) arity
          (layout.frameWireMap ∘ ports)
    | .identity origin arity ports =>
        .identity (layout.frameNode origin) arity
          (layout.frameWireMap ∘ ports)
    | .cut body => .cut (layout.graftFrameRegion material body)
    | .bubble arity body =>
        .bubble arity (layout.graftFrameRegion material body)

  def graftFrameItems (layout : PlugLayout input)
      (material : CompiledRegion input.pattern.val.diagram) :
      CompiledItems input.frame.val → CompiledItems layout.plugRaw
    | .nil => .nil
    | .cons head tail => .cons
        (layout.graftFrameItem material head)
        (layout.graftFrameItems material tail)

  /-- Map terminal material identities into their dense target allocations.
  Administrative spine regions are not copied. -/
  def graftPatternRegion (layout : PlugLayout input) :
      CompiledRegion input.pattern.val.diagram → CompiledRegion layout.plugRaw
    | .mk origin nodes children =>
        .mk (layout.bodyRegion origin)
          (layout.graftPatternItems nodes)
          (layout.graftPatternItems children)

  def graftPatternItem (layout : PlugLayout input) :
      CompiledItem input.pattern.val.diagram → CompiledItem layout.plugRaw
    | .atom origin binder arity ports =>
        .atom (layout.patternNode origin) (layout.binderRegion binder) arity
          (layout.patternWireMap ∘ ports)
    | .identity origin arity ports =>
        .identity (layout.patternNode origin) arity
          (layout.patternWireMap ∘ ports)
    | .cut body => .cut (layout.graftPatternRegion body)
    | .bubble arity body =>
        .bubble arity (layout.graftPatternRegion body)

  def graftPatternItems (layout : PlugLayout input) :
      CompiledItems input.pattern.val.diagram → CompiledItems layout.plugRaw
    | .nil => .nil
    | .cons head tail => .cons
        (layout.graftPatternItem head) (layout.graftPatternItems tail)
end

@[simp] theorem graftFrameRegion_origin (layout : PlugLayout input)
    (material : CompiledRegion input.pattern.val.diagram)
    (region : CompiledRegion input.frame.val) :
    (layout.graftFrameRegion material region).origin =
      layout.frameRegion region.origin := by
  cases region with
  | mk origin nodes children =>
      by_cases site : origin = input.site <;>
        simp [graftFrameRegion, site, CompiledRegion.origin]

@[simp] theorem graftFrameItem_origin (layout : PlugLayout input)
    (material : CompiledRegion input.pattern.val.diagram)
    (item : CompiledItem input.frame.val) :
    (layout.graftFrameItem material item).origin =
      layout.mapFrameOccurrence item.origin := by
  cases item with
  | atom => rfl
  | identity => rfl
  | cut body =>
      change LocalOccurrence.child
        (layout.graftFrameRegion material body).origin =
          LocalOccurrence.child (layout.frameRegion body.origin)
      exact congrArg LocalOccurrence.child
        (layout.graftFrameRegion_origin material body)
  | bubble arity body =>
      change LocalOccurrence.child
        (layout.graftFrameRegion material body).origin =
          LocalOccurrence.child (layout.frameRegion body.origin)
      exact congrArg LocalOccurrence.child
        (layout.graftFrameRegion_origin material body)

@[simp] theorem graftFrameItems_origins (layout : PlugLayout input)
    (material : CompiledRegion input.pattern.val.diagram)
    (items : CompiledItems input.frame.val) :
    (layout.graftFrameItems material items).origins =
      items.origins.map layout.mapFrameOccurrence :=
  match items with
  | .nil => rfl
  | .cons head tail => by
      change
        (layout.graftFrameItem material head).origin ::
            (layout.graftFrameItems material tail).origins =
          layout.mapFrameOccurrence head.origin ::
            tail.origins.map layout.mapFrameOccurrence
      rw [layout.graftFrameItem_origin material head,
        layout.graftFrameItems_origins material tail]
      rfl

@[simp] theorem graftPatternRegion_origin (layout : PlugLayout input)
    (region : CompiledRegion input.pattern.val.diagram) :
    (layout.graftPatternRegion region).origin =
      layout.bodyRegion region.origin := by
  cases region
  rfl

@[simp] theorem graftPatternItem_origin (layout : PlugLayout input)
    (item : CompiledItem input.pattern.val.diagram) :
    (layout.graftPatternItem item).origin =
      layout.mapPatternOccurrence item.origin := by
  cases item with
  | atom => rfl
  | identity => rfl
  | cut body =>
      change LocalOccurrence.child (layout.graftPatternRegion body).origin =
        LocalOccurrence.child (layout.bodyRegion body.origin)
      exact congrArg LocalOccurrence.child
        (layout.graftPatternRegion_origin body)
  | bubble arity body =>
      change LocalOccurrence.child (layout.graftPatternRegion body).origin =
        LocalOccurrence.child (layout.bodyRegion body.origin)
      exact congrArg LocalOccurrence.child
        (layout.graftPatternRegion_origin body)

@[simp] theorem graftPatternItems_origins (layout : PlugLayout input)
    (items : CompiledItems input.pattern.val.diagram) :
    (layout.graftPatternItems items).origins =
      items.origins.map layout.mapPatternOccurrence :=
  match items with
  | .nil => rfl
  | .cons head tail => by
      change
        (layout.graftPatternItem head).origin ::
            (layout.graftPatternItems tail).origins =
          layout.mapPatternOccurrence head.origin ::
            tail.origins.map layout.mapPatternOccurrence
      rw [layout.graftPatternItem_origin head,
        layout.graftPatternItems_origins tail]
      rfl

/-- Pattern binders keep their arity.  Material binders use their dense
region image; lexical proxy binders use the caller-supplied frame target. -/
theorem plugRaw_binder_bubble (layout : PlugLayout input)
    (admissible : input.Admissible)
    {binder parent : Fin input.pattern.val.diagram.regionCount}
    {arity : Nat}
    (shape : input.pattern.val.diagram.regions binder =
      .bubble parent arity) :
    ∃ targetParent,
      layout.plugRaw.regions (layout.binderRegion binder) =
        .bubble targetParent arity := by
  by_cases material : input.binderSpine.IsMaterialRegion binder
  · let carrier := layout.materialCarrier binder material
    have origin : layout.materialRegions.origin carrier = binder :=
      layout.materialCarrier_origin binder material
    refine ⟨layout.bodyRegion parent, ?_⟩
    rw [← origin, layout.binderRegion_materialOrigin,
      layout.plugRaw_regions_material, origin, shape]
    rfl
  · have binderNeRoot : binder ≠ input.pattern.val.diagram.root := by
      intro equality
      rw [equality, input.pattern.property.diagram_well_formed.root_is_sheet]
        at shape
      contradiction
    have notEveryProxy : ¬∀ index, binder ≠ input.binderSpine.proxy index :=
      fun noProxy => material ⟨binderNeRoot, noProxy⟩
    obtain ⟨index, notNe⟩ := Classical.not_forall.mp notEveryProxy
    have binderEq : binder = input.binderSpine.proxy index :=
      Classical.not_not.mp notNe
    subst binder
    have proxyShape := input.binderSpine.proxy_region index
    have arityEq : input.binderSpine.arity index = arity := by
      exact (CRegion.bubble.inj (proxyShape.symm.trans shape)).2
    obtain ⟨targetParent, targetShape⟩ :=
      admissible.binder_targets_match index
    refine ⟨layout.frameRegion targetParent, ?_⟩
    rw [layout.binderRegion_proxy, layout.plugRaw_regions_frame, targetShape]
    simp [PlugLayout.mapFrameRegion, arityEq]
    rfl

private theorem patternChild_isMaterial
    {input : Splice.Input} {parent child : Fin input.pattern.val.diagram.regionCount}
    (parentSource : parent = input.binderSpine.bodyContainer ∨
      input.binderSpine.IsMaterialRegion parent)
    (parentEq : (input.pattern.val.diagram.regions child).parent? =
      some parent) :
    input.binderSpine.IsMaterialRegion child := by
  rcases parentSource with rfl | material
  · exact directBodyChild_isMaterial input child parentEq
  · exact directMaterialChild_isMaterial input parent child material parentEq

mutual
  theorem graftPatternRegion_valid (layout : PlugLayout input)
      (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
      (region : CompiledRegion input.pattern.val.diagram)
      (valid : region.Valid)
      (material : input.binderSpine.IsMaterialRegion region.origin) :
      (layout.graftPatternRegion region).Valid := by
    cases region with
    | mk origin nodes children =>
        change _ ∧ _ ∧ _ ∧ _
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [layout.graftPatternItems_origins, valid.1,
            layout.map_localNodeOccurrences_materialSource origin material]
          exact (layout.localNodeOccurrences_materialSource origin material).symm
        · rw [layout.graftPatternItems_origins, valid.2.1,
            layout.map_localChildOccurrences_materialSource origin material]
          exact (layout.localChildOccurrences_materialSource origin material).symm
        · exact layout.graftPatternItems_validAt admissible targetWf origin
            (Or.inr material) nodes valid.2.2.1
        · exact layout.graftPatternItems_validAt admissible targetWf origin
            (Or.inr material) children valid.2.2.2

  theorem graftPatternItem_validAt (layout : PlugLayout input)
      (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
      (parent : Fin input.pattern.val.diagram.regionCount)
      (parentSource : parent = input.binderSpine.bodyContainer ∨
        input.binderSpine.IsMaterialRegion parent)
      (item : CompiledItem input.pattern.val.diagram)
      (valid : item.ValidAt parent) :
      (layout.graftPatternItem item).ValidAt (layout.bodyRegion parent) := by
    cases item with
    | atom origin binder arity ports =>
        have targetNode : layout.plugRaw.nodes (layout.patternNode origin) =
            .atom (layout.bodyRegion parent) (layout.binderRegion binder) := by
          rw [layout.plugRaw_nodes_pattern, valid.1]
          rfl
        obtain ⟨targetParent, targetBinder⟩ :=
          layout.plugRaw_binder_bubble admissible valid.2.1
        refine ⟨targetNode, ?_, ?_, ?_⟩
        · rw [bubbleParent_of_bubble targetBinder]
          exact targetBinder
        · have encloses := targetWf.atom_binders_enclose
              (layout.patternNode origin)
          rw [targetNode] at encloses
          exact encloses
        · intro index
          exact layout.endpointOccurs_pattern (valid.2.2.2 index)
    | identity origin arity ports =>
        refine ⟨?_, ?_⟩
        · rw [layout.plugRaw_nodes_pattern, valid.1]
          rfl
        · intro index
          exact layout.endpointOccurs_pattern (valid.2 index)
    | cut body =>
        have parentEq : (input.pattern.val.diagram.regions body.origin).parent? =
            some parent := by simp [valid.1, CRegion.parent?]
        have childMaterial := patternChild_isMaterial parentSource parentEq
        refine ⟨?_, layout.graftPatternRegion_valid admissible targetWf body
          valid.2 childMaterial⟩
        rw [layout.graftPatternRegion_origin body,
          layout.plugRaw_regions_materialSource body.origin childMaterial,
          valid.1]
        rfl
    | bubble arity body =>
        have parentEq : (input.pattern.val.diagram.regions body.origin).parent? =
            some parent := by simp [valid.1, CRegion.parent?]
        have childMaterial := patternChild_isMaterial parentSource parentEq
        refine ⟨?_, layout.graftPatternRegion_valid admissible targetWf body
          valid.2 childMaterial⟩
        rw [layout.graftPatternRegion_origin body,
          layout.plugRaw_regions_materialSource body.origin childMaterial,
          valid.1]
        rfl

  theorem graftPatternItems_validAt (layout : PlugLayout input)
      (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
      (parent : Fin input.pattern.val.diagram.regionCount)
      (parentSource : parent = input.binderSpine.bodyContainer ∨
        input.binderSpine.IsMaterialRegion parent)
      (items : CompiledItems input.pattern.val.diagram)
      (valid : items.ValidAt parent) :
      (layout.graftPatternItems items).ValidAt (layout.bodyRegion parent) := by
    cases items with
    | nil => trivial
    | cons head tail =>
        exact ⟨layout.graftPatternItem_validAt admissible targetWf parent
          parentSource head valid.1,
          layout.graftPatternItems_validAt admissible targetWf parent
            parentSource tail valid.2⟩
end

private theorem region_node_origins (region : CompiledRegion d)
    (valid : region.Valid) :
    region.nodeItems.origins = localNodeOccurrences d region.origin := by
  cases region
  exact valid.1

private theorem region_child_origins (region : CompiledRegion d)
    (valid : region.Valid) :
    region.childItems.origins = localChildOccurrences d region.origin := by
  cases region
  exact valid.2.1

private theorem region_nodes_valid (region : CompiledRegion d)
    (valid : region.Valid) : region.nodeItems.ValidAt region.origin := by
  cases region
  exact valid.2.2.1

private theorem region_children_valid (region : CompiledRegion d)
    (valid : region.Valid) : region.childItems.ValidAt region.origin := by
  cases region
  exact valid.2.2.2

mutual
  theorem graftFrameRegion_valid (layout : PlugLayout input)
      (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
      (material : CompiledRegion input.pattern.val.diagram)
      (materialValid : material.Valid)
      (materialOrigin : material.origin = input.binderSpine.bodyContainer)
      (region : CompiledRegion input.frame.val) (valid : region.Valid) :
      (layout.graftFrameRegion material region).Valid := by
    cases region with
    | mk origin nodes children =>
        by_cases site : origin = input.site
        · subst origin
          simp only [graftFrameRegion]
          change _ ∧ _ ∧ _ ∧ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [CompiledItems.origins_append,
              layout.graftFrameItems_origins,
              layout.graftPatternItems_origins, valid.1,
              region_node_origins material materialValid,
              materialOrigin, layout.map_localNodeOccurrences_frame,
              layout.map_localNodeOccurrences_body,
              layout.localNodeOccurrences_frameRegion,
              layout.patternNodeOccurrences_site admissible]
            rfl
          · rw [CompiledItems.origins_append,
              layout.graftFrameItems_origins,
              layout.graftPatternItems_origins, valid.2.1,
              region_child_origins material materialValid, materialOrigin,
              layout.map_localChildOccurrences_frame,
              layout.map_localChildOccurrences_body,
              layout.localChildOccurrences_frameRegion,
              layout.materialChildOccurrences_site admissible]
            rfl
          · exact CompiledItems.valid_append _ _
              (layout.graftFrameItems_validAt admissible targetWf material
                materialValid materialOrigin input.site nodes valid.2.2.1)
              (by simpa using
                (layout.graftPatternItems_validAt admissible targetWf
                  input.binderSpine.bodyContainer (Or.inl rfl)
                  material.nodeItems
                    (materialOrigin ▸ region_nodes_valid material materialValid)))
          · exact CompiledItems.valid_append _ _
              (layout.graftFrameItems_validAt admissible targetWf material
                materialValid materialOrigin input.site children valid.2.2.2)
              (by simpa using
                (layout.graftPatternItems_validAt admissible targetWf
                  input.binderSpine.bodyContainer (Or.inl rfl)
                  material.childItems
                    (materialOrigin ▸ region_children_valid material materialValid)))
        · simp only [graftFrameRegion, if_neg site]
          change _ ∧ _ ∧ _ ∧ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [layout.graftFrameItems_origins, valid.1,
              layout.map_localNodeOccurrences_frame,
              layout.localNodeOccurrences_frameRegion,
              layout.patternNodeOccurrences_eq_nil_of_ne_site origin site]
            simp
          · rw [layout.graftFrameItems_origins, valid.2.1,
              layout.map_localChildOccurrences_frame,
              layout.localChildOccurrences_frameRegion,
              layout.materialChildOccurrences_eq_nil_of_ne_site origin site]
            simp
          · exact layout.graftFrameItems_validAt admissible targetWf material
              materialValid materialOrigin origin nodes valid.2.2.1
          · exact layout.graftFrameItems_validAt admissible targetWf material
              materialValid materialOrigin origin children valid.2.2.2

  theorem graftFrameItem_validAt (layout : PlugLayout input)
      (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
      (material : CompiledRegion input.pattern.val.diagram)
      (materialValid : material.Valid)
      (materialOrigin : material.origin = input.binderSpine.bodyContainer)
      (parent : Fin input.frame.val.regionCount)
      (item : CompiledItem input.frame.val) (valid : item.ValidAt parent) :
      (layout.graftFrameItem material item).ValidAt
        (layout.frameRegion parent) := by
    cases item with
    | atom origin binder arity ports =>
        have targetNode : layout.plugRaw.nodes (layout.frameNode origin) =
            .atom (layout.frameRegion parent) (layout.frameRegion binder) := by
          rw [layout.plugRaw_nodes_frame, valid.1]
          rfl
        have targetBinder : layout.plugRaw.regions
            (layout.frameRegion binder) =
            .bubble (layout.frameRegion (bubbleParent input.frame.val binder))
              arity := by
          rw [layout.plugRaw_regions_frame, valid.2.1]
          simp [PlugLayout.mapFrameRegion]
          rfl
        refine ⟨targetNode, ?_, ?_, ?_⟩
        · rw [bubbleParent_of_bubble targetBinder]
          exact targetBinder
        · have encloses := targetWf.atom_binders_enclose
              (layout.frameNode origin)
          rw [targetNode] at encloses
          exact encloses
        · intro index
          exact layout.endpointOccurs_frame (valid.2.2.2 index)
    | identity origin arity ports =>
        refine ⟨?_, ?_⟩
        · rw [layout.plugRaw_nodes_frame, valid.1]
          rfl
        · intro index
          exact layout.endpointOccurs_frame (valid.2 index)
    | cut body =>
        refine ⟨?_, layout.graftFrameRegion_valid admissible targetWf material
          materialValid materialOrigin body valid.2⟩
        rw [layout.graftFrameRegion_origin,
          layout.plugRaw_regions_frame, valid.1]
        rfl
    | bubble arity body =>
        refine ⟨?_, layout.graftFrameRegion_valid admissible targetWf material
          materialValid materialOrigin body valid.2⟩
        rw [layout.graftFrameRegion_origin,
          layout.plugRaw_regions_frame, valid.1]
        rfl

  theorem graftFrameItems_validAt (layout : PlugLayout input)
      (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
      (material : CompiledRegion input.pattern.val.diagram)
      (materialValid : material.Valid)
      (materialOrigin : material.origin = input.binderSpine.bodyContainer)
      (parent : Fin input.frame.val.regionCount)
      (items : CompiledItems input.frame.val) (valid : items.ValidAt parent) :
      (layout.graftFrameItems material items).ValidAt
        (layout.frameRegion parent) := by
    cases items with
    | nil => trivial
    | cons head tail =>
        exact ⟨layout.graftFrameItem_validAt admissible targetWf material
          materialValid materialOrigin parent head valid.1,
          layout.graftFrameItems_validAt admissible targetWf material
            materialValid materialOrigin parent tail valid.2⟩
end

end Splice.Input.PlugLayout

namespace Elaboration

private theorem eq_singleton_of_nodup
    {values : List α} {value : α}
    (nodup : values.Nodup) (member : value ∈ values)
    (only : ∀ other, other ∈ values → other = value) :
    values = [value] := by
  cases values with
  | nil => simp at member
  | cons head tail =>
      have headEq : head = value := only head (by simp)
      subst head
      have tailEq : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro other otherMember
        have otherEq : other = value := only other (by simp [otherMember])
        subst other
        exact (List.nodup_cons.mp nodup).1 otherMember
      subst tail
      rfl

private theorem terminal_hiddenWires_eq_nil
    (input : Splice.Input) (terminal : input.TerminalBody)
    (nonempty : input.binderSpine.proxyCount ≠ 0) :
    input.pattern.val.hiddenWires = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire hiddenMember
  have hidden := (OpenDiagram.mem_hiddenWires input.pattern.val wire).mp
    hiddenMember
  have notBoundary : wire ∉ input.pattern.val.boundary := by
    intro boundary
    exact hidden.2 ((OpenDiagram.mem_exposedWires input.pattern.val wire).mpr
      boundary)
  exact terminal.root_has_no_nonboundary_wires nonempty wire notBoundary
    hidden.1

private theorem terminal_root_localNodeOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (nonempty : input.binderSpine.proxyCount ≠ 0) :
    localNodeOccurrences input.pattern.val.diagram
      input.pattern.val.diagram.root = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro occurrence member
  cases occurrence with
  | node node =>
      exact terminal.root_has_no_nodes nonempty node
        ((mem_localNodeOccurrences_node input.pattern.val.diagram
          input.pattern.val.diagram.root node).mp member)
  | child child => exact (not_mem_localNodeOccurrences_child _ _ _) member

private theorem terminal_root_localChildOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (nonempty : input.binderSpine.proxyCount ≠ 0) :
    localChildOccurrences input.pattern.val.diagram
        input.pattern.val.diagram.root =
      [.child (input.binderSpine.proxy
        ⟨0, Nat.pos_of_ne_zero nonempty⟩)] := by
  let first : Fin input.binderSpine.proxyCount :=
    ⟨0, Nat.pos_of_ne_zero nonempty⟩
  apply eq_singleton_of_nodup
    (localChildOccurrences_nodup input.pattern.val.diagram
      input.pattern.val.diagram.root)
  · apply (mem_localChildOccurrences_child input.pattern.val.diagram
      input.pattern.val.diagram.root (input.binderSpine.proxy first)).mpr
    rw [input.binderSpine.proxy_region first]
    rfl
  · intro occurrence member
    cases occurrence with
    | node node =>
        exfalso
        exact (not_mem_localChildOccurrences_node _ _ _) member
    | child child =>
        exact congrArg LocalOccurrence.child
          (terminal.root_direct_child nonempty child
            ((mem_localChildOccurrences_child input.pattern.val.diagram
              input.pattern.val.diagram.root child).mp member))

private theorem terminal_nonterminal_localNodeOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (nonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    localNodeOccurrences input.pattern.val.diagram
      (input.binderSpine.proxy proxy) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro occurrence member
  cases occurrence with
  | node node =>
      exact terminal.nonterminal_has_no_nodes proxy nonterminal node
        ((mem_localNodeOccurrences_node input.pattern.val.diagram
          (input.binderSpine.proxy proxy) node).mp member)
  | child child => exact (not_mem_localNodeOccurrences_child _ _ _) member

private theorem terminal_nonterminal_exactScopeWires_eq_nil
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (nonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    exactScopeWires input.pattern.val.diagram
      (input.binderSpine.proxy proxy) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire member
  have scope := (mem_exactScopeWires input.pattern.val.diagram
    (input.binderSpine.proxy proxy) wire).mp member
  by_cases boundary : wire ∈ input.pattern.val.boundary
  · have rootScope := terminal.boundary_is_root_scoped wire boundary
    exact input.binderSpine.proxy_ne_root proxy (scope.symm.trans rootScope)
  · exact terminal.nonterminal_has_no_nonboundary_wires proxy nonterminal
      wire boundary scope

private theorem terminal_nonterminal_localChildOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (nonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    localChildOccurrences input.pattern.val.diagram
        (input.binderSpine.proxy proxy) =
      [.child (input.binderSpine.proxy
        ⟨proxy.val + 1, nonterminal⟩)] := by
  let next : Fin input.binderSpine.proxyCount :=
    ⟨proxy.val + 1, nonterminal⟩
  apply eq_singleton_of_nodup
    (localChildOccurrences_nodup input.pattern.val.diagram
      (input.binderSpine.proxy proxy))
  · apply (mem_localChildOccurrences_child input.pattern.val.diagram
      (input.binderSpine.proxy proxy)
      (input.binderSpine.proxy next)).mpr
    rw [input.binderSpine.proxy_region next]
    simp [next]
    rfl
  · intro occurrence member
    cases occurrence with
    | node node =>
        exfalso
        exact (not_mem_localChildOccurrences_node _ _ _) member
    | child child =>
        exact congrArg LocalOccurrence.child
          (terminal.nonterminal_direct_child proxy nonterminal child
            ((mem_localChildOccurrences_child input.pattern.val.diagram
              (input.binderSpine.proxy proxy) child).mp member))

private theorem region_eq_singletonBubble
    {d : Diagram} (region : CompiledRegion d) (valid : region.Valid)
    {origin child : Fin d.regionCount} {arity : Nat}
    (originEq : region.origin = origin)
    (nodesEq : localNodeOccurrences d origin = [])
    (childrenEq : localChildOccurrences d origin = [.child child])
    (childShape : d.regions child = .bubble origin arity) :
    ∃ body, region = .mk origin .nil (.cons (.bubble arity body) .nil) ∧
      body.origin = child ∧ body.Valid := by
  cases region with
  | mk actual nodes children =>
      change actual = origin at originEq
      subst actual
      have nodesOrigins : nodes.origins = [] := valid.1.trans nodesEq
      cases nodes with
      | nil =>
          have childrenOrigins : children.origins = [.child child] :=
            valid.2.1.trans childrenEq
          cases children with
          | nil => simp at childrenOrigins
          | cons head tail =>
              have headOrigin : head.origin = .child child :=
                (List.cons.inj childrenOrigins).1
              have tailOrigins : tail.origins = [] :=
                (List.cons.inj childrenOrigins).2
              cases tail with
              | nil =>
                  cases head with
                  | atom => contradiction
                  | identity => contradiction
                  | cut body =>
                      have bodyOrigin : body.origin = child :=
                        LocalOccurrence.child.inj headOrigin
                      have impossible := valid.2.2.2.1.1.symm.trans
                        (bodyOrigin ▸ childShape)
                      contradiction
                  | bubble bodyArity body =>
                      have bodyOrigin : body.origin = child :=
                        LocalOccurrence.child.inj headOrigin
                      have shapeEq := valid.2.2.2.1.1.symm.trans
                        (bodyOrigin ▸ childShape)
                      have arityEq : bodyArity = arity :=
                        (CRegion.bubble.inj shapeEq).2
                      subst bodyArity
                      exact ⟨body, rfl, bodyOrigin,
                        valid.2.2.2.1.2⟩
              | cons tailHead tailTail => simp at tailOrigins
      | cons head tail => simp at nodesOrigins

private theorem focusHere_outerContext
    {d : Diagram} {site : Fin d.regionCount}
    (region : CompiledRegion d) (environment : CompiledEnvironment region)
    (hwf : d.WellFormed) (originEq : region.origin = site)
    {focus : CompiledFocus region site}
    (found : region.focus? site = some focus) :
    (focus.zipper.intrinsic environment hwf).environment.outer =
      environment.outer := by
  rw [CompiledRegion.focus?] at found
  simp [originEq] at found
  cases found
  rfl

private theorem terminalProxy_outerContext
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (region : CompiledRegion input.pattern.val.diagram)
    (valid : region.Valid)
    (originEq : region.origin = input.binderSpine.proxy proxy)
    (environment : CompiledEnvironment region)
    (outerEq : environment.outer = input.pattern.val.exposedWires)
    (localsEq : proxy.val + 1 < input.binderSpine.proxyCount →
      environment.locals = [])
    {focus : CompiledFocus region input.binderSpine.bodyContainer}
    (found : region.focus? input.binderSpine.bodyContainer = some focus) :
    (focus.zipper.intrinsic environment
      input.pattern.property.diagram_well_formed).environment.outer =
        input.pattern.val.exposedWires := by
  by_cases terminalProxy : proxy.val + 1 = input.binderSpine.proxyCount
  · have nonempty : input.binderSpine.proxyCount ≠ 0 := by
      have := proxy.isLt
      omega
    have bodyEq : input.binderSpine.bodyContainer =
        input.binderSpine.proxy proxy := by
      rw [input.binderSpine.body_eq_terminal_of_nonempty nonempty]
      apply congrArg input.binderSpine.proxy
      apply Fin.ext
      simp
      omega
    have endpointEq : region.origin = input.binderSpine.bodyContainer :=
      originEq.trans bodyEq.symm
    rw [CompiledRegion.focus?] at found
    simp [endpointEq] at found
    cases found
    exact outerEq
  · have nonterminal : proxy.val + 1 < input.binderSpine.proxyCount := by
      omega
    let next : Fin input.binderSpine.proxyCount :=
      ⟨proxy.val + 1, nonterminal⟩
    have nextShape : input.pattern.val.diagram.regions
        (input.binderSpine.proxy next) =
      .bubble (input.binderSpine.proxy proxy)
        (input.binderSpine.arity next) := by
      rw [input.binderSpine.proxy_region next]
      simp [next]
    obtain ⟨nextBody, regionShape, nextOrigin, nextValid⟩ :=
      region_eq_singletonBubble region valid originEq
        (terminal_nonterminal_localNodeOccurrences input terminal proxy
          nonterminal)
        (terminal_nonterminal_localChildOccurrences input terminal proxy
          nonterminal) nextShape
    subst region
    have different : input.binderSpine.proxy proxy ≠
        input.binderSpine.bodyContainer := by
      intro equality
      have nonempty : input.binderSpine.proxyCount ≠ 0 := by
        have := proxy.isLt
        omega
      rw [input.binderSpine.body_eq_terminal_of_nonempty nonempty] at equality
      have indexEq := input.binderSpine.proxy_injective equality
      have values := congrArg Fin.val indexEq
      simp at values
      omega
    rw [CompiledRegion.focus?_singleton_bubble nextBody different] at found
    cases nextFound : nextBody.focus? input.binderSpine.bodyContainer with
    | none => simp [nextFound] at found
    | some nextFocus =>
        simp only [nextFound, Option.map_some, Option.some.injEq] at found
        subst focus
        have bodyShape : input.pattern.val.diagram.regions nextBody.origin =
            .bubble (input.binderSpine.proxy proxy)
              (input.binderSpine.arity next) := by
          rw [nextOrigin]
          exact nextShape
        let nextEnvironment : CompiledEnvironment nextBody := {
          outer := environment.fullContext
          locals := exactScopeWires input.pattern.val.diagram nextBody.origin
          rels := input.binderSpine.arity next :: environment.rels
          binders := environment.binders.push nextBody.origin
            (input.binderSpine.arity next)
          valid := nextValid
          exact := environment.exact.extend_child
            input.pattern.property.diagram_well_formed (by
              rw [bodyShape]
              rfl)
          covers := BinderContext.push_covers_bubble_child environment.covers
            bodyShape
          enumeration := environment.enumeration.bubbleChild
            input.pattern.property.diagram_well_formed bodyShape
        }
        have nextOuter : nextEnvironment.outer =
            input.pattern.val.exposedWires := by
          simp [nextEnvironment, CompiledEnvironment.fullContext,
            outerEq, localsEq nonterminal]
        have nextLocals : next.val + 1 < input.binderSpine.proxyCount →
            nextEnvironment.locals = [] := by
          intro nextNonterminal
          change exactScopeWires input.pattern.val.diagram nextBody.origin = []
          rw [nextOrigin]
          exact terminal_nonterminal_exactScopeWires_eq_nil input terminal next
            nextNonterminal
        have recursive := terminalProxy_outerContext input terminal next
          nextBody nextValid nextOrigin
          nextEnvironment nextOuter nextLocals nextFound
        simpa [CompiledZipper.intrinsic, CompiledItemsZipper.intrinsic,
          nextEnvironment] using recursive
termination_by input.binderSpine.proxyCount - proxy.val

private theorem terminalRoot_outerContext
    (input : Splice.Input) (terminal : input.TerminalBody)
    (nonempty : input.binderSpine.proxyCount ≠ 0)
    (region : CompiledRegion input.pattern.val.diagram)
    (valid : region.Valid)
    (originEq : region.origin = input.pattern.val.diagram.root)
    (environment : CompiledEnvironment region)
    (outerEq : environment.outer = input.pattern.val.exposedWires)
    (localsEq : environment.locals = [])
    {focus : CompiledFocus region input.binderSpine.bodyContainer}
    (found : region.focus? input.binderSpine.bodyContainer = some focus) :
    (focus.zipper.intrinsic environment
      input.pattern.property.diagram_well_formed).environment.outer =
        input.pattern.val.exposedWires := by
  let first : Fin input.binderSpine.proxyCount :=
    ⟨0, Nat.pos_of_ne_zero nonempty⟩
  have firstShape : input.pattern.val.diagram.regions
      (input.binderSpine.proxy first) =
    .bubble input.pattern.val.diagram.root
      (input.binderSpine.arity first) := by
    rw [input.binderSpine.proxy_region first]
    simp [first]
  obtain ⟨firstBody, regionShape, firstOrigin, firstValid⟩ :=
    region_eq_singletonBubble region valid originEq
      (terminal_root_localNodeOccurrences input terminal nonempty)
      (terminal_root_localChildOccurrences input terminal nonempty) firstShape
  subst region
  have different : input.pattern.val.diagram.root ≠
      input.binderSpine.bodyContainer := by
    intro equality
    rw [input.binderSpine.body_eq_terminal_of_nonempty nonempty] at equality
    exact input.binderSpine.proxy_ne_root _ equality.symm
  rw [CompiledRegion.focus?_singleton_bubble firstBody different] at found
  cases firstFound : firstBody.focus? input.binderSpine.bodyContainer with
  | none => simp [firstFound] at found
  | some firstFocus =>
      simp only [firstFound, Option.map_some, Option.some.injEq] at found
      subst focus
      have bodyShape : input.pattern.val.diagram.regions firstBody.origin =
          .bubble input.pattern.val.diagram.root
            (input.binderSpine.arity first) := by
        rw [firstOrigin]
        exact firstShape
      let firstEnvironment : CompiledEnvironment firstBody := {
        outer := environment.fullContext
        locals := exactScopeWires input.pattern.val.diagram firstBody.origin
        rels := input.binderSpine.arity first :: environment.rels
        binders := environment.binders.push firstBody.origin
          (input.binderSpine.arity first)
        valid := firstValid
        exact := environment.exact.extend_child
          input.pattern.property.diagram_well_formed (by
            rw [bodyShape]
            rfl)
        covers := BinderContext.push_covers_bubble_child environment.covers
          bodyShape
        enumeration := environment.enumeration.bubbleChild
          input.pattern.property.diagram_well_formed bodyShape
      }
      have firstOuter : firstEnvironment.outer =
          input.pattern.val.exposedWires := by
        simp [firstEnvironment, CompiledEnvironment.fullContext,
          outerEq, localsEq]
      have firstLocals : first.val + 1 < input.binderSpine.proxyCount →
          firstEnvironment.locals = [] := by
        intro firstNonterminal
        change exactScopeWires input.pattern.val.diagram firstBody.origin = []
        rw [firstOrigin]
        exact terminal_nonterminal_exactScopeWires_eq_nil input terminal first
          firstNonterminal
      have recursive := terminalProxy_outerContext input terminal first
        firstBody firstValid firstOrigin firstEnvironment firstOuter firstLocals
        firstFound
      simpa [CompiledZipper.intrinsic, CompiledItemsZipper.intrinsic,
        firstEnvironment] using recursive

/-- The terminal material inherits exactly the pattern's exposed wire block;
administrative spine regions contribute no local wires. -/
theorem patternTerminal_outerContext
    (input : Splice.Input) (terminal : input.TerminalBody) :
    CompiledSite.outerContext (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer = input.pattern.val.exposedWires := by
  let patternState := State.ofOpen input.pattern
  let focus := CompiledSite.focus patternState input.binderSpine.bodyContainer
  have found : input.pattern.compilation.focus?
      input.binderSpine.bodyContainer = some focus := by
    change patternState.checked.compilation.focus?
      input.binderSpine.bodyContainer = some
        (CompiledSite.focus patternState input.binderSpine.bodyContainer)
    exact CompiledSite.focus_computation patternState
      input.binderSpine.bodyContainer
  change (focus.zipper.intrinsic (CompiledSite.rootEnvironment patternState)
    input.pattern.property.diagram_well_formed).environment.outer = _
  by_cases empty : input.binderSpine.proxyCount = 0
  · have bodyEq := input.binderSpine.body_eq_root_of_empty empty
    have endpointEq : input.pattern.compilation.origin =
        input.binderSpine.bodyContainer := by
      rw [VisualProof.Concrete.CheckedOpen.compilation_origin, bodyEq]
    exact (focusHere_outerContext input.pattern.compilation
      (CompiledSite.rootEnvironment patternState)
      input.pattern.property.diagram_well_formed endpointEq found).trans rfl
  · exact terminalRoot_outerContext input terminal empty input.pattern.compilation
      input.pattern.compilation_valid
      (VisualProof.Concrete.CheckedOpen.compilation_origin input.pattern)
      (CompiledSite.rootEnvironment patternState) rfl
      (by simpa [patternState, CompiledSite.rootEnvironment] using
        terminal_hiddenWires_eq_nil input terminal empty)
      found

private noncomputable def terminalRelationBinders (input : Splice.Input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  let enumeration := CompiledSite.binders_enumeration
    (State.ofOpen input.pattern) input.binderSpine.bodyContainer
  (allFin (CompiledSite.rels (State.ofOpen input.pattern)
    input.binderSpine.bodyContainer).length).map enumeration.binder

private def terminalProxies (input : Splice.Input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  (allFin input.binderSpine.proxyCount).map input.binderSpine.proxy

private theorem terminalRelationBinders_nodup (input : Splice.Input) :
    (terminalRelationBinders input).Nodup := by
  apply (allFin_nodup _).map
  intro left right different equal
  exact different ((CompiledSite.binders_enumeration
    (State.ofOpen input.pattern)
    input.binderSpine.bodyContainer).binder_injective equal)

private theorem terminalProxies_nodup (input : Splice.Input) :
    (terminalProxies input).Nodup := by
  apply (allFin_nodup _).map
  intro left right different equal
  exact different (input.binderSpine.proxy_injective equal)

private theorem terminalBinder_mem_iff_proxy_mem
    (input : Splice.Input)
    (binder : Fin input.pattern.val.diagram.regionCount) :
    binder ∈ terminalProxies input ↔
      binder ∈ terminalRelationBinders input := by
  let patternState := State.ofOpen input.pattern
  let enumeration := CompiledSite.binders_enumeration patternState
    input.binderSpine.bodyContainer
  constructor
  · intro proxyMember
    obtain ⟨proxy, _, proxyEq⟩ := List.mem_map.mp proxyMember
    let parent := if _zero : proxy.val = 0 then
      input.pattern.val.diagram.root
    else input.binderSpine.proxy ⟨proxy.val - 1, by omega⟩
    have shape := input.binderSpine.proxy_region proxy
    change input.pattern.val.diagram.regions (input.binderSpine.proxy proxy) =
      .bubble parent (input.binderSpine.arity proxy) at shape
    obtain ⟨relation, lookup⟩ :=
      CompiledSite.binders_covers patternState
        input.binderSpine.bodyContainer
        (input.binderSpine.proxy proxy) parent
        (input.binderSpine.arity proxy) shape
        (input.binderSpine.proxy_encloses_bodyContainer proxy)
    apply List.mem_map.mpr
    refine ⟨relation.index, mem_allFin relation.index, ?_⟩
    exact (enumeration.lookup_owner relation lookup).trans proxyEq
  · intro relationMember
    obtain ⟨relation, _, relationEq⟩ := List.mem_map.mp relationMember
    obtain ⟨parent, bubble⟩ := enumeration.bubble relation
    obtain ⟨proxy, proxyEq⟩ :=
      input.binderSpine.enclosing_bubble_eq_proxy
        input.pattern.property.diagram_well_formed bubble
        (enumeration.encloses relation)
    apply List.mem_map.mpr
    exact ⟨proxy, mem_allFin proxy, proxyEq.symm.trans relationEq⟩

private theorem terminalRelationBinders_length (input : Splice.Input) :
    (terminalRelationBinders input).length =
      (CompiledSite.rels (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).length := by
  simp [terminalRelationBinders, allFin_eq_finRange]

private theorem terminalProxies_length (input : Splice.Input) :
    (terminalProxies input).length = input.binderSpine.proxyCount := by
  simp [terminalProxies, allFin_eq_finRange]

private noncomputable def terminalRelationProxyIndexEquiv (input : Splice.Input) :
    FiniteEquiv (Fin (terminalRelationBinders input).length)
      (Fin (terminalProxies input).length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin input.pattern.val.diagram.regionCount))
    (terminalRelationBinders input) (terminalProxies input)
    (terminalRelationBinders_nodup input) (terminalProxies_nodup input)
    (by
      intro binder
      simpa only [FiniteEquiv.refl_apply] using
        terminalBinder_mem_iff_proxy_mem input binder)

/-- Concrete proxy corresponding to one terminal material relation position. -/
noncomputable def terminalRelationProxyEquiv (input : Splice.Input) :
    FiniteEquiv
      (Fin (CompiledSite.rels (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).length)
      (Fin input.binderSpine.proxyCount) :=
  (FiniteEquiv.finCast (terminalRelationBinders_length input).symm).trans
    ((terminalRelationProxyIndexEquiv input).trans
      (FiniteEquiv.finCast (terminalProxies_length input)))

theorem terminalRelationProxyEquiv_binder (input : Splice.Input)
    (relation : Fin (CompiledSite.rels (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).length) :
    input.binderSpine.proxy (terminalRelationProxyEquiv input relation) =
      (CompiledSite.binders_enumeration (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).binder relation := by
  have spec := FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin input.pattern.val.diagram.regionCount))
    (terminalRelationBinders input) (terminalProxies input)
    (terminalRelationBinders_nodup input) (terminalProxies_nodup input)
    (by
      intro binder
      simpa only [FiniteEquiv.refl_apply] using
        terminalBinder_mem_iff_proxy_mem input binder)
    (FiniteEquiv.finCast (terminalRelationBinders_length input).symm relation)
  simpa [terminalRelationProxyEquiv, terminalRelationProxyIndexEquiv,
    terminalRelationBinders, terminalProxies, FiniteEquiv.finCast,
    allFin_eq_finRange] using spec

theorem terminalRelationProxyEquiv_arity (input : Splice.Input)
    (relation : Fin (CompiledSite.rels (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).length) :
    (CompiledSite.rels (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).get relation =
      input.binderSpine.arity (terminalRelationProxyEquiv input relation) := by
  let enumeration := CompiledSite.binders_enumeration
    (State.ofOpen input.pattern) input.binderSpine.bodyContainer
  obtain ⟨parent, bubble⟩ := enumeration.bubble relation
  have proxyShape := input.binderSpine.proxy_region
    (terminalRelationProxyEquiv input relation)
  rw [terminalRelationProxyEquiv_binder input relation] at proxyShape
  exact (CRegion.bubble.inj (bubble.symm.trans proxyShape)).2

theorem terminalRelationProxyEquiv_lookup (input : Splice.Input)
    (relation : RelVar
      (CompiledSite.rels (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer) arity) :
    CompiledSite.binders (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer
        (input.binderSpine.proxy
          (terminalRelationProxyEquiv input relation.index)) =
      some ⟨arity, relation⟩ := by
  cases relation with
  | mk index hasArity =>
      cases hasArity
      rw [terminalRelationProxyEquiv_binder input index]
      simpa using (CompiledSite.binders_enumeration
        (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).lookup index

end Elaboration

end VisualProof.Concrete
