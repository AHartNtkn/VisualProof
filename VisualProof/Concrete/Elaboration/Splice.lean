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

end VisualProof.Concrete
