import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Presentation.Core

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace TwoInputPresentation

/-- Source frame regions retain their identity in the target plug layout;
source-only pattern material is opaque and maps to the distinguished site. -/
def regionMap (presentation : TwoInputPresentation source target) :
    Fin source.plugLayout.plugRaw.regionCount →
      Fin target.plugLayout.plugRaw.regionCount :=
  Fin.addCases
    (fun region => target.plugLayout.frameRegion
      (Fin.cast presentation.frameRegionCountEq region))
    (fun _ => target.plugLayout.frameRegion target.site)

@[simp] theorem regionMap_frameRegion
    (presentation : TwoInputPresentation source target)
    (region : Fin source.frame.val.regionCount) :
    presentation.regionMap (source.plugLayout.frameRegion region) =
      target.plugLayout.frameRegion
        (Fin.cast presentation.frameRegionCountEq region) := by
  simp [regionMap, Input.PlugLayout.frameRegion, Input.PlugLayout.plugRaw,
    Input.PlugLayout.regionCount]

@[simp] theorem regionMap_site
    (presentation : TwoInputPresentation source target) :
    presentation.regionMap
        (source.plugLayout.frameRegion source.site) =
      target.plugLayout.frameRegion target.site := by
  rw [presentation.regionMap_frameRegion, presentation.site_eq]

theorem regionMap_root
    (presentation : TwoInputPresentation source target) :
    target.plugLayout.plugRaw.root =
      presentation.regionMap source.plugLayout.plugRaw.root := by
  change target.plugLayout.frameRegion target.frame.val.root =
    presentation.regionMap
      (source.plugLayout.frameRegion source.frame.val.root)
  rw [presentation.regionMap_frameRegion]
  exact congrArg target.plugLayout.frameRegion
    (checkedDiagram_root_eq source.frame target.frame presentation.frame_eq).symm

/-- The shared simulation owns every source-pattern region opaquely.  The
retained splice site is distinguished as well because it contains the complete
local replacement, even when the pattern has no surviving material region. -/
def Distinguished (presentation : TwoInputPresentation source target)
    (region : Fin source.plugLayout.plugRaw.regionCount) : Prop :=
  region = source.plugLayout.frameRegion source.site ∨
    ∃ material : source.plugLayout.materialRegions.Carrier,
      region = source.plugLayout.materialRegion material

/-- A proper nested splice leaves the enclosing root in the regular,
retained-frame part of the paired traversal. -/
theorem root_not_distinguished_of_nested
    (presentation : TwoInputPresentation source target)
    (hnested : source.site ≠ source.frame.val.root) :
    ¬ presentation.Distinguished source.plugLayout.plugRaw.root := by
  change ¬ presentation.Distinguished
    (source.plugLayout.frameRegion source.frame.val.root)
  rintro (rootAtSite | ⟨material, rootMaterial⟩)
  · exact hnested
      (source.plugLayout.frameRegion_injective rootAtSite).symm
  · exact source.plugLayout.frameRegion_ne_materialRegion
      source.frame.val.root material rootMaterial

theorem distinguished_bodyRegion
    (presentation : TwoInputPresentation source target)
    (region : Fin source.pattern.val.diagram.regionCount) :
    presentation.Distinguished (source.plugLayout.bodyRegion region) := by
  unfold Distinguished PlugLayout.bodyRegion
  split
  · rename_i material hmaterial
    exact Or.inr ⟨material, rfl⟩
  · exact Or.inl rfl

/-- Every non-distinguished region is retained-frame material away from the
splice site. -/
theorem regularFrameRegion
    (presentation : TwoInputPresentation source target)
    (region : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished region) :
    ∃ frame : Fin source.frame.val.regionCount,
      frame ≠ source.site ∧
        region = source.plugLayout.frameRegion frame := by
  revert regular
  refine Fin.addCases (m := source.frame.val.regionCount)
    (n := source.plugLayout.materialRegions.count) (fun frame => ?_)
    (fun material => ?_) region
  · intro regular
    refine ⟨frame, ?_, rfl⟩
    intro equality
    apply regular
    subst frame
    exact Or.inl rfl
  · intro regular
    exact False.elim (regular (Or.inr ⟨material, rfl⟩))

/-- A child of a regular retained-frame region is itself retained-frame
material.  Pattern material can only occur below the distinguished splice
site. -/
theorem regularChildFrameRegion
    (presentation : TwoInputPresentation source target)
    (parent child : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished parent)
    (childParent : (source.plugLayout.plugRaw.regions child).parent? =
      some parent) :
    ∃ frameChild : Fin source.frame.val.regionCount,
      child = source.plugLayout.frameRegion frameChild := by
  obtain ⟨frameParent, hne, rfl⟩ :=
    presentation.regularFrameRegion parent regular
  revert childParent
  refine Fin.addCases (m := source.frame.val.regionCount)
    (n := source.plugLayout.materialRegions.count) (fun frameChild => ?_)
    (fun materialChild => ?_) child
  · intro _
    exact ⟨frameChild, rfl⟩
  · intro childParent
    have member : ConcreteElaboration.LocalOccurrence.child
        (source.plugLayout.materialRegion materialChild) ∈
          ConcreteElaboration.localOccurrences source.plugLayout.plugRaw
            (source.plugLayout.frameRegion frameParent) :=
      (ConcreteElaboration.mem_localOccurrences_child _ _ _).2 childParent
    obtain ⟨original, _, mapped⟩ :=
      source.plugLayout.frameSemanticOccurrences_complete frameParent hne
        _ member
    cases original with
    | node frameNode => contradiction
    | child frameChild =>
        exact False.elim
          (source.plugLayout.frameRegion_ne_materialRegion frameChild
            materialChild
            (ConcreteElaboration.LocalOccurrence.child.inj mapped))

private theorem filter_frameNodes
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    List.filter
        (fun node => decide
          ((layout.plugNode node).region = layout.frameRegion region))
        ((VisualProof.Data.Finite.allFin input.frame.val.nodeCount).map
          layout.frameNode) =
      ((VisualProof.Data.Finite.allFin input.frame.val.nodeCount).filter
        fun node => decide ((input.frame.val.nodes node).region = region)).map
          layout.frameNode := by
  rw [List.filter_map]
  apply congrArg (List.map layout.frameNode)
  apply congrArg (fun predicate =>
    List.filter predicate
      (VisualProof.Data.Finite.allFin input.frame.val.nodeCount))
  funext node
  simp [layout.plugNode_frameNode, layout.frameRegion_eq_iff]

private theorem filter_frameChildren
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    List.filter
        (fun child => decide
          ((layout.plugRegion child).parent? = some (layout.frameRegion region)))
        ((VisualProof.Data.Finite.allFin input.frame.val.regionCount).map
          layout.frameRegion) =
      ((VisualProof.Data.Finite.allFin input.frame.val.regionCount).filter
        fun child => decide
          ((input.frame.val.regions child).parent? = some region)).map
            layout.frameRegion := by
  rw [List.filter_map]
  apply congrArg (List.map layout.frameRegion)
  apply congrArg (fun predicate =>
    List.filter predicate
      (VisualProof.Data.Finite.allFin input.frame.val.regionCount))
  funext child
  change decide ((layout.plugRegion (layout.frameRegion child)).parent? =
    some (layout.frameRegion region)) = _
  rw [layout.plugRegion_frameRegion]
  cases hkind : input.frame.val.regions child <;>
    simp [hkind, PlugLayout.mapFrameRegion, CRegion.parent?,
      layout.frameRegion_eq_iff]

private theorem filter_patternNodes_eq_nil
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount)
    (hne : region ≠ input.site) :
    List.filter
        (fun node => decide
          ((layout.plugNode node).region = layout.frameRegion region))
        ((VisualProof.Data.Finite.allFin
          input.pattern.val.diagram.nodeCount).map layout.patternNode) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro node hnode
  rw [List.mem_filter] at hnode
  obtain ⟨hnode, selected⟩ := hnode
  rw [List.mem_map] at hnode
  obtain ⟨patternNode, _, rfl⟩ := hnode
  have member : ConcreteElaboration.LocalOccurrence.node
      (layout.patternNode patternNode) ∈
        ConcreteElaboration.localOccurrences layout.plugRaw
          (layout.frameRegion region) :=
    (ConcreteElaboration.mem_localOccurrences_node _ _ _).2
      (decide_eq_true_iff.mp selected)
  obtain ⟨original, _, mapped⟩ :=
    layout.frameSemanticOccurrences_complete region hne _ member
  cases original with
  | node frameNode =>
      exact layout.frameNode_ne_patternNode frameNode patternNode
        (ConcreteElaboration.LocalOccurrence.node.inj mapped)
  | child frameChild => contradiction

private theorem filter_materialChildren_eq_nil
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount)
    (hne : region ≠ input.site) :
    List.filter
        (fun child => decide
          ((layout.plugRegion child).parent? = some (layout.frameRegion region)))
        ((VisualProof.Data.Finite.allFin layout.materialRegions.count).map
          layout.materialRegion) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro child hchild
  rw [List.mem_filter] at hchild
  obtain ⟨hchild, selected⟩ := hchild
  rw [List.mem_map] at hchild
  obtain ⟨materialChild, _, rfl⟩ := hchild
  have member : ConcreteElaboration.LocalOccurrence.child
      (layout.materialRegion materialChild) ∈
        ConcreteElaboration.localOccurrences layout.plugRaw
          (layout.frameRegion region) :=
    (ConcreteElaboration.mem_localOccurrences_child _ _ _).2
      (decide_eq_true_iff.mp selected)
  obtain ⟨original, _, mapped⟩ :=
    layout.frameSemanticOccurrences_complete region hne _ member
  cases original with
  | node frameNode => contradiction
  | child frameChild =>
      exact layout.frameRegion_ne_materialRegion frameChild materialChild
        (ConcreteElaboration.LocalOccurrence.child.inj mapped)

theorem localOccurrences_frameRegion
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount)
    (hne : region ≠ input.site) :
    ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion region) =
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw region).map
        layout.mapFrameOccurrence := by
  unfold ConcreteElaboration.localOccurrences
    VisualProof.Data.Finite.filterFin
  change
    ((VisualProof.Data.Finite.allFin
      (input.frame.val.nodeCount + input.pattern.val.diagram.nodeCount)).filter
        fun node => decide
          ((layout.plugNode node).region = layout.frameRegion region)).map
            ConcreteElaboration.LocalOccurrence.node ++
      ((VisualProof.Data.Finite.allFin
        (input.frame.val.regionCount + layout.materialRegions.count)).filter
        fun child => decide
          ((layout.plugRegion child).parent? =
            some (layout.frameRegion region))).map
              ConcreteElaboration.LocalOccurrence.child =
    ((((VisualProof.Data.Finite.allFin input.frame.val.nodeCount).filter
      fun node => decide ((input.frame.val.nodes node).region = region)).map
        ConcreteElaboration.LocalOccurrence.node ++
      ((VisualProof.Data.Finite.allFin input.frame.val.regionCount).filter
      fun child => decide
        ((input.frame.val.regions child).parent? = some region)).map
          ConcreteElaboration.LocalOccurrence.child).map
            layout.mapFrameOccurrence)
  rw [show VisualProof.Data.Finite.allFin
        (input.frame.val.nodeCount + input.pattern.val.diagram.nodeCount) =
      (VisualProof.Data.Finite.allFin input.frame.val.nodeCount).map
          layout.frameNode ++
        (VisualProof.Data.Finite.allFin
          input.pattern.val.diagram.nodeCount).map layout.patternNode from
      paired_allFin_layout_nodes layout,
    show VisualProof.Data.Finite.allFin
        (input.frame.val.regionCount + layout.materialRegions.count) =
      (VisualProof.Data.Finite.allFin input.frame.val.regionCount).map
          layout.frameRegion ++
        (VisualProof.Data.Finite.allFin layout.materialRegions.count).map
          layout.materialRegion from paired_allFin_layout_regions layout]
  calc
    _ =
        ((List.filter
          (fun node => decide
            ((layout.plugNode node).region = layout.frameRegion region))
          ((VisualProof.Data.Finite.allFin input.frame.val.nodeCount).map
            layout.frameNode)).map ConcreteElaboration.LocalOccurrence.node ++
        (List.filter
          (fun node => decide
            ((layout.plugNode node).region = layout.frameRegion region))
          ((VisualProof.Data.Finite.allFin
            input.pattern.val.diagram.nodeCount).map layout.patternNode)).map
              ConcreteElaboration.LocalOccurrence.node) ++
        ((List.filter
          (fun child => decide
            ((layout.plugRegion child).parent? =
              some (layout.frameRegion region)))
          ((VisualProof.Data.Finite.allFin input.frame.val.regionCount).map
            layout.frameRegion)).map
              ConcreteElaboration.LocalOccurrence.child ++
        (List.filter
          (fun child => decide
            ((layout.plugRegion child).parent? =
              some (layout.frameRegion region)))
          ((VisualProof.Data.Finite.allFin layout.materialRegions.count).map
            layout.materialRegion)).map
              ConcreteElaboration.LocalOccurrence.child) := by
      congr 1
      · exact (congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
            (List.filter_append
              (p := fun node => decide
                ((layout.plugNode node).region = layout.frameRegion region))
              ((VisualProof.Data.Finite.allFin
                input.frame.val.nodeCount).map layout.frameNode)
              ((VisualProof.Data.Finite.allFin
                input.pattern.val.diagram.nodeCount).map
                  layout.patternNode))).trans List.map_append
      · exact (congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
            (List.filter_append
              (p := fun child => decide
                ((layout.plugRegion child).parent? =
                  some (layout.frameRegion region)))
              ((VisualProof.Data.Finite.allFin
                input.frame.val.regionCount).map layout.frameRegion)
              ((VisualProof.Data.Finite.allFin
                layout.materialRegions.count).map
                  layout.materialRegion))).trans List.map_append
    _ = _ := by
      simp only [filter_frameNodes,
        filter_patternNodes_eq_nil layout region hne,
        filter_frameChildren,
        filter_materialChildren_eq_nil layout region hne,
        List.map_nil, List.append_nil, List.map_append, List.map_map]
      let sourceNodes :=
        (VisualProof.Data.Finite.allFin input.frame.val.nodeCount).filter
          fun node => decide ((input.frame.val.nodes node).region = region)
      let sourceChildren :=
        (VisualProof.Data.Finite.allFin input.frame.val.regionCount).filter
          fun child => decide
            ((input.frame.val.regions child).parent? = some region)
      change
        List.map (ConcreteElaboration.LocalOccurrence.node ∘ layout.frameNode)
            sourceNodes ++
          List.map (ConcreteElaboration.LocalOccurrence.child ∘
            layout.frameRegion) sourceChildren =
        List.map layout.mapFrameOccurrence
          (List.map ConcreteElaboration.LocalOccurrence.node sourceNodes ++
            List.map ConcreteElaboration.LocalOccurrence.child sourceChildren)
      calc
        _ = List.map (layout.mapFrameOccurrence ∘
              ConcreteElaboration.LocalOccurrence.node) sourceNodes ++
            List.map (layout.mapFrameOccurrence ∘
              ConcreteElaboration.LocalOccurrence.child) sourceChildren := by
          congr 1 <;> apply List.map_congr_left <;> intro occurrence _ <;> rfl
        _ = List.map layout.mapFrameOccurrence
              (List.map ConcreteElaboration.LocalOccurrence.node sourceNodes) ++
            List.map layout.mapFrameOccurrence
              (List.map ConcreteElaboration.LocalOccurrence.child
                sourceChildren) := by
          congr 1
          · exact List.map_map.symm
          · exact List.map_map.symm
        _ = _ := List.map_append.symm

/-- The total occurrence map sends retained-frame occurrences positionally.
Pattern occurrences are arbitrary outside their distinguished owner, so a
pattern node is represented by the distinguished target child; the regular
node theorem below proves that this branch is never semantically traversed. -/
def occurrenceMap (presentation : TwoInputPresentation source target)
    (region : Fin source.plugLayout.plugRaw.regionCount)
    (_regular : ¬ presentation.Distinguished region) :
    ConcreteElaboration.LocalOccurrence source.plugLayout.plugRaw.regionCount
        source.plugLayout.plugRaw.nodeCount →
      ConcreteElaboration.LocalOccurrence target.plugLayout.plugRaw.regionCount
        target.plugLayout.plugRaw.nodeCount
  | .node node =>
      Fin.addCases
        (fun frameNode => .node (target.plugLayout.frameNode
          (Fin.cast presentation.frameNodeCountEq frameNode)))
        (fun _ => .child (target.plugLayout.frameRegion target.site)) node
  | .child child => .child (presentation.regionMap child)

/-- Retained-frame nodes have the same computational payload at the focused
site; only their region and binder identities are transported through the
paired frame equality. -/
def mapFrameNodeShape
    (presentation : TwoInputPresentation source target) :
    CNode source.plugLayout.plugRaw.regionCount →
      CNode target.plugLayout.plugRaw.regionCount
  | .term region freePorts term =>
      .term (presentation.regionMap region) freePorts term
  | .atom region binder =>
      .atom (presentation.regionMap region)
        (presentation.regionMap binder)
  | .named region definition arity =>
      .named (presentation.regionMap region) definition arity

theorem frameNode_shape
    (presentation : TwoInputPresentation source target)
    (node : Fin source.frame.val.nodeCount) :
    target.plugLayout.plugRaw.nodes
        (target.plugLayout.frameNode
          (Fin.cast presentation.frameNodeCountEq node)) =
      presentation.mapFrameNodeShape
        (source.plugLayout.plugRaw.nodes
          (source.plugLayout.frameNode node)) := by
  change target.plugLayout.plugNode
      (target.plugLayout.frameNode
        (Fin.cast presentation.frameNodeCountEq node)) =
    presentation.mapFrameNodeShape
      (source.plugLayout.plugNode
        (source.plugLayout.frameNode node))
  rw [source.plugLayout.plugNode_frameNode,
    target.plugLayout.plugNode_frameNode,
    checkedDiagram_nodes_rename_eq source.frame target.frame
      presentation.frame_eq node]
  cases hnode : source.frame.val.nodes node <;>
    simp [hnode, mapFrameNodeShape, PlugLayout.mapFrameNode, CNode.rename,
      FiniteEquiv.finCast, presentation.regionMap_frameRegion]
  all_goals rfl

theorem occurrenceMap_child
    (presentation : TwoInputPresentation source target)
    (region : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished region)
    (child : Fin source.plugLayout.plugRaw.regionCount) :
    presentation.occurrenceMap region regular (.child child) =
      .child (presentation.regionMap child) := by
  rfl

theorem occurrenceMap_node
    (presentation : TwoInputPresentation source target)
    (region : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished region)
    (node : Fin source.plugLayout.plugRaw.nodeCount)
    (nodeRegion : (source.plugLayout.plugRaw.nodes node).region = region) :
    ∃ targetNode,
      presentation.occurrenceMap region regular (.node node) =
        .node targetNode := by
  revert nodeRegion
  refine Fin.addCases (m := source.frame.val.nodeCount)
    (n := source.pattern.val.diagram.nodeCount) (fun frameNode => ?_)
    (fun patternNode => ?_) node
  · intro nodeRegion
    exact ⟨target.plugLayout.frameNode
      (Fin.cast presentation.frameNodeCountEq frameNode), by
        simp [occurrenceMap]⟩
  · intro nodeRegion
    have patternRegion : source.plugLayout.bodyRegion
        (source.pattern.val.diagram.nodes patternNode).region = region := by
      simpa [PlugLayout.plugRaw, PlugLayout.plugNode,
        PlugLayout.mapPatternNode_region] using nodeRegion
    exact False.elim
      (regular (patternRegion ▸ presentation.distinguished_bodyRegion
        (source.pattern.val.diagram.nodes patternNode).region))

theorem occurrenceMap_mapFrameOccurrence
    (presentation : TwoInputPresentation source target)
    (frame : Fin source.frame.val.regionCount)
    (regular : ¬ presentation.Distinguished
      (source.plugLayout.frameRegion frame))
    (occurrence : ConcreteElaboration.LocalOccurrence
      source.frame.val.regionCount source.frame.val.nodeCount) :
    presentation.occurrenceMap (source.plugLayout.frameRegion frame) regular
        (source.plugLayout.mapFrameOccurrence occurrence) =
      target.plugLayout.mapFrameOccurrence
        (castLocalOccurrence source.frame target.frame
          presentation.frameRegionCountEq presentation.frameNodeCountEq
          occurrence) := by
  cases occurrence with
  | node node =>
      simp [occurrenceMap, PlugLayout.mapFrameOccurrence, castLocalOccurrence,
        PlugLayout.frameNode, PlugLayout.plugRaw, PlugLayout.nodeCount]
  | child child =>
      change ConcreteElaboration.LocalOccurrence.child
          (presentation.regionMap
            (source.plugLayout.frameRegion child)) =
        ConcreteElaboration.LocalOccurrence.child
          (target.plugLayout.frameRegion
            (Fin.cast presentation.frameRegionCountEq child))
      rw [presentation.regionMap_frameRegion]
      rfl

theorem localOccurrences_map
    (presentation : TwoInputPresentation source target)
    (region : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished region) :
    ConcreteElaboration.localOccurrences target.plugLayout.plugRaw
        (presentation.regionMap region) =
      (ConcreteElaboration.localOccurrences source.plugLayout.plugRaw
        region).map (presentation.occurrenceMap region regular) := by
  obtain ⟨frame, hne, rfl⟩ :=
    presentation.regularFrameRegion region regular
  let targetFrame := Fin.cast presentation.frameRegionCountEq frame
  have targetNe : targetFrame ≠ target.site := by
    intro equality
    apply hne
    apply Fin.ext
    have values := congrArg Fin.val
      (equality.trans presentation.site_eq.symm)
    exact values
  rw [presentation.regionMap_frameRegion,
    localOccurrences_frameRegion target.plugLayout targetFrame targetNe,
    localOccurrences_frameRegion source.plugLayout frame hne]
  have frameOccurrences := checkedDiagram_localOccurrences_eq
    source.frame target.frame presentation.frame_eq frame
  change ConcreteElaboration.localOccurrences target.coalesceFrameRaw
      targetFrame =
    (ConcreteElaboration.localOccurrences source.coalesceFrameRaw frame).map
      (castLocalOccurrence source.frame target.frame
        presentation.frameRegionCountEq presentation.frameNodeCountEq)
      at frameOccurrences
  rw [frameOccurrences]
  calc
    _ = List.map (target.plugLayout.mapFrameOccurrence ∘
          castLocalOccurrence source.frame target.frame
            presentation.frameRegionCountEq presentation.frameNodeCountEq)
        (ConcreteElaboration.localOccurrences source.coalesceFrameRaw frame) :=
      List.map_map
    _ = List.map
        (presentation.occurrenceMap (source.plugLayout.frameRegion frame)
          regular ∘ source.plugLayout.mapFrameOccurrence)
        (ConcreteElaboration.localOccurrences source.coalesceFrameRaw frame) := by
      apply List.map_congr_left
      intro occurrence _
      exact (presentation.occurrenceMap_mapFrameOccurrence frame regular
        occurrence).symm
    _ = _ := List.map_map.symm

def mapRegionKind
    (presentation : TwoInputPresentation source target) :
    CRegion source.plugLayout.plugRaw.regionCount →
      CRegion target.plugLayout.plugRaw.regionCount
  | .sheet => .sheet
  | .cut sourceParent => .cut (presentation.regionMap sourceParent)
  | .bubble sourceParent arity =>
      .bubble (presentation.regionMap sourceParent) arity

/-- A retained-frame child keeps its cut/bubble wrapper even when its parent is
the distinguished splice site.  Regular-parent provenance is unnecessary for
this frame-only fact. -/
theorem region_shape_frameRegion
    (presentation : TwoInputPresentation source target)
    (frameChild : Fin source.frame.val.regionCount) :
    target.plugLayout.plugRaw.regions
        (presentation.regionMap
          (source.plugLayout.frameRegion frameChild)) =
      presentation.mapRegionKind
        (source.plugLayout.plugRaw.regions
          (source.plugLayout.frameRegion frameChild)) := by
  rw [presentation.regionMap_frameRegion]
  change target.plugLayout.plugRegion
      (target.plugLayout.frameRegion
        (Fin.cast presentation.frameRegionCountEq frameChild)) =
    presentation.mapRegionKind
      (source.plugLayout.plugRegion
        (source.plugLayout.frameRegion frameChild))
  rw [source.plugLayout.plugRegion_frameRegion,
    target.plugLayout.plugRegion_frameRegion]
  have payload := checkedDiagram_regions_rename_eq source.frame target.frame
    presentation.frame_eq frameChild
  rw [payload]
  cases hkind : source.frame.val.regions frameChild <;>
    simp [hkind, CRegion.rename, PlugLayout.mapFrameRegion, mapRegionKind,
      presentation.regionMap_frameRegion, FiniteEquiv.finCast] <;> rfl

theorem region_shape
    (presentation : TwoInputPresentation source target)
    (parent : Fin source.plugLayout.plugRaw.regionCount)
    (regular : ¬ presentation.Distinguished parent)
    (child : Fin source.plugLayout.plugRaw.regionCount)
    (childParent : (source.plugLayout.plugRaw.regions child).parent? =
      some parent) :
    target.plugLayout.plugRaw.regions (presentation.regionMap child) =
      presentation.mapRegionKind
        (source.plugLayout.plugRaw.regions child) := by
  obtain ⟨frameParent, hne, rfl⟩ :=
    presentation.regularFrameRegion parent regular
  revert childParent
  refine Fin.addCases (m := source.frame.val.regionCount)
    (n := source.plugLayout.materialRegions.count) (fun frameChild => ?_)
    (fun materialChild => ?_) child
  · intro childParent
    change target.plugLayout.plugRaw.regions
        (presentation.regionMap
          (source.plugLayout.frameRegion frameChild)) =
      presentation.mapRegionKind
        (source.plugLayout.plugRaw.regions
          (source.plugLayout.frameRegion frameChild))
    rw [presentation.regionMap_frameRegion]
    change target.plugLayout.plugRegion
        (target.plugLayout.frameRegion
          (Fin.cast presentation.frameRegionCountEq frameChild)) =
      presentation.mapRegionKind
        (source.plugLayout.plugRegion
          (source.plugLayout.frameRegion frameChild))
    rw [source.plugLayout.plugRegion_frameRegion,
      target.plugLayout.plugRegion_frameRegion]
    have payload := checkedDiagram_regions_rename_eq source.frame target.frame
      presentation.frame_eq frameChild
    rw [payload]
    cases hkind : source.frame.val.regions frameChild <;>
      simp [hkind, CRegion.rename, PlugLayout.mapFrameRegion, mapRegionKind,
        presentation.regionMap_frameRegion, FiniteEquiv.finCast] <;> rfl
  · intro childParent
    have member : ConcreteElaboration.LocalOccurrence.child
        (source.plugLayout.materialRegion materialChild) ∈
          ConcreteElaboration.localOccurrences source.plugLayout.plugRaw
            (source.plugLayout.frameRegion frameParent) :=
      (ConcreteElaboration.mem_localOccurrences_child _ _ _).2 childParent
    obtain ⟨original, _, mapped⟩ :=
      source.plugLayout.frameSemanticOccurrences_complete frameParent hne
        _ member
    cases original with
    | node frameNode => contradiction
    | child frameChild =>
        exact False.elim
          (source.plugLayout.frameRegion_ne_materialRegion frameChild
            materialChild
            (ConcreteElaboration.LocalOccurrence.child.inj mapped))

/-- Binder environments agree exactly on retained-frame bubble identities,
transported through the proof that the two presentations share a frame.
Pattern binders are owned by the distinguished focused kernel. -/
def BinderRelated {rels : VisualProof.Theory.RelCtx}
    (presentation : TwoInputPresentation source target)
    (sourceBinders : ConcreteElaboration.BinderContext
      source.plugLayout.plugRaw rels)
    (targetBinders : ConcreteElaboration.BinderContext
      target.plugLayout.plugRaw rels) : Prop :=
  ∀ frame : Fin source.frame.val.regionCount,
    sourceBinders (source.plugLayout.frameRegion frame) =
      targetBinders (target.plugLayout.frameRegion
        (Fin.cast presentation.frameRegionCountEq frame))

/-- Heterogeneous binder evidence for the generalized compiler simulation.
The relation contexts are propositionally equal, while retained-frame lookup
agreement is recorded with `HEq` so the witness remains well-typed before
that equality is eliminated. -/
structure BinderWitness
    (presentation : TwoInputPresentation source target)
    {sourceRels targetRels : VisualProof.Theory.RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      source.plugLayout.plugRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      target.plugLayout.plugRaw targetRels) : Type where
  relationContexts_eq : sourceRels = targetRels
  related : ∀ frame : Fin source.frame.val.regionCount,
    HEq (sourceBinders (source.plugLayout.frameRegion frame))
      (targetBinders (target.plugLayout.frameRegion
        (Fin.cast presentation.frameRegionCountEq frame)))

namespace BinderWitness

def relationMap
    (witness : BinderWitness (sourceRels := sourceRels)
      (targetRels := targetRels) presentation sourceBinders targetBinders) :
    RelationRenaming sourceRels targetRels := by
  rcases witness with ⟨relationContextsEq, related⟩
  subst targetRels
  exact ConcreteElaboration.identityRelationRenaming sourceRels

theorem related_of_same_context
    (witness : BinderWitness presentation sourceBinders targetBinders) :
    presentation.BinderRelated sourceBinders targetBinders := by
  intro frame
  exact eq_of_heq (witness.related frame)

end BinderWitness

theorem binders_empty
    (presentation : TwoInputPresentation source target) :
    presentation.BinderRelated ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty := by
  intro frame
  rfl

def binderWitness_empty
    (presentation : TwoInputPresentation source target) :
    presentation.BinderWitness ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty where
  relationContexts_eq := rfl
  related := fun _ => HEq.rfl

/-- Pushing a retained-frame bubble preserves binder agreement even when the
bubble is a direct child of the distinguished splice site. -/
theorem binders_push_frameRegion
    (presentation : TwoInputPresentation source target)
    {rels : VisualProof.Theory.RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      source.plugLayout.plugRaw rels}
    {targetBinders : ConcreteElaboration.BinderContext
      target.plugLayout.plugRaw rels}
    (related : presentation.BinderRelated sourceBinders targetBinders)
    (frameChild : Fin source.frame.val.regionCount)
    (arity : Nat) :
    presentation.BinderRelated
      (sourceBinders.push
        (source.plugLayout.frameRegion frameChild) arity)
      (targetBinders.push
        (target.plugLayout.frameRegion
          (Fin.cast presentation.frameRegionCountEq frameChild)) arity) := by
  intro frame
  by_cases hframe : frame = frameChild
  · subst frame
    rw [ConcreteElaboration.BinderContext.push_self,
      ConcreteElaboration.BinderContext.push_self]
  · have sourceNe :
        source.plugLayout.frameRegion frame ≠
          source.plugLayout.frameRegion frameChild := by
      intro equality
      exact hframe (source.plugLayout.frameRegion_injective equality)
    have targetNe :
        target.plugLayout.frameRegion
            (Fin.cast presentation.frameRegionCountEq frame) ≠
          target.plugLayout.frameRegion
            (Fin.cast presentation.frameRegionCountEq frameChild) := by
      intro equality
      apply hframe
      apply Fin.ext
      have values := congrArg Fin.val
        (target.plugLayout.frameRegion_injective equality)
      exact values
    rw [ConcreteElaboration.BinderContext.push_other _ arity sourceNe,
      ConcreteElaboration.BinderContext.push_other _ arity targetNe,
      related frame]

theorem binders_push
    (presentation : TwoInputPresentation source target)
    {rels : VisualProof.Theory.RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      source.plugLayout.plugRaw rels}
    {targetBinders : ConcreteElaboration.BinderContext
      target.plugLayout.plugRaw rels}
    (related : presentation.BinderRelated sourceBinders targetBinders)
    (child parent : Fin source.plugLayout.plugRaw.regionCount)
    (arity : Nat)
    (childKind : source.plugLayout.plugRaw.regions child =
      .bubble parent arity)
    (regular : ¬ presentation.Distinguished parent) :
    presentation.BinderRelated
      (sourceBinders.push child arity)
      (targetBinders.push (presentation.regionMap child) arity) := by
  have childParent :
      (source.plugLayout.plugRaw.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨frameChild, rfl⟩ :=
    presentation.regularChildFrameRegion parent child regular childParent
  intro frame
  by_cases hframe : frame = frameChild
  · subst frame
    rw [ConcreteElaboration.BinderContext.push_self,
      presentation.regionMap_frameRegion,
      ConcreteElaboration.BinderContext.push_self]
  · have sourceNe :
        source.plugLayout.frameRegion frame ≠
          source.plugLayout.frameRegion frameChild := by
      intro equality
      exact hframe (source.plugLayout.frameRegion_injective equality)
    have targetNe :
        target.plugLayout.frameRegion
            (Fin.cast presentation.frameRegionCountEq frame) ≠
          presentation.regionMap
            (source.plugLayout.frameRegion frameChild) := by
      rw [presentation.regionMap_frameRegion]
      intro equality
      apply hframe
      apply Fin.ext
      have values := congrArg Fin.val
        (target.plugLayout.frameRegion_injective equality)
      exact values
    rw [ConcreteElaboration.BinderContext.push_other _ arity sourceNe,
      ConcreteElaboration.BinderContext.push_other _ arity targetNe,
      related frame]

def binderWitness_push
    (presentation : TwoInputPresentation source target)
    {sourceRels targetRels : VisualProof.Theory.RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      source.plugLayout.plugRaw sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      target.plugLayout.plugRaw targetRels}
    (witness : presentation.BinderWitness sourceBinders targetBinders)
    (child parent : Fin source.plugLayout.plugRaw.regionCount)
    (arity : Nat)
    (childKind : source.plugLayout.plugRaw.regions child =
      .bubble parent arity)
    (regular : ¬ presentation.Distinguished parent) :
    presentation.BinderWitness
      (sourceBinders.push child arity)
      (targetBinders.push (presentation.regionMap child) arity) := by
  cases witness with
  | mk relationContexts_eq related =>
      subst targetRels
      have relatedEq : presentation.BinderRelated sourceBinders targetBinders :=
        fun frame => eq_of_heq (related frame)
      have pushed := presentation.binders_push relatedEq child parent arity
        childKind regular
      exact ⟨rfl, fun frame => heq_of_eq (pushed frame)⟩

theorem binderWitness_relationMap_push
    (presentation : TwoInputPresentation source target)
    {sourceRels targetRels : VisualProof.Theory.RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      source.plugLayout.plugRaw sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      target.plugLayout.plugRaw targetRels}
    (witness : presentation.BinderWitness sourceBinders targetBinders)
    (child parent : Fin source.plugLayout.plugRaw.regionCount)
    (arity : Nat)
    (childKind : source.plugLayout.plugRaw.regions child =
      .bubble parent arity)
    (regular : ¬ presentation.Distinguished parent) :
    (BinderWitness.relationMap
        (presentation.binderWitness_push witness child parent arity childKind
          regular) : RelationRenaming (arity :: sourceRels)
            (arity :: targetRels)) =
      (RelationRenaming.lift (BinderWitness.relationMap witness) arity :
        RelationRenaming (arity :: sourceRels)
          (arity :: targetRels)) := by
  cases witness with
  | mk relationContexts_eq related =>
      subst targetRels
      simpa [BinderWitness.relationMap, binderWitness_push,
        ConcreteElaboration.identityRelationRenaming] using
          (RelationRenaming.lift_id_fun
            (source := sourceRels) arity).symm

private def depthAllowed
    (siteDirection direction : ConcreteElaboration.SimulationDirection)
    (depth : Nat) : Prop :=
  match siteDirection, direction with
  | .forward, .forward | .backward, .backward => depth % 2 = 0
  | .forward, .backward | .backward, .forward => depth % 2 = 1

/-- A direction is admissible at a source region when every route from that
region to the distinguished splice site has the parity required to arrive in
the citation's focused direction.  Regions outside the site's ancestor chain
have no such route, so the condition is intentionally vacuous there. -/
def Allowed
    (presentation : TwoInputPresentation source target)
    (siteDirection direction : ConcreteElaboration.SimulationDirection)
    (region : Fin source.plugLayout.plugRaw.regionCount) : Prop :=
  ∀ {path depth}
    (route : RegionRoute source.plugLayout.plugRaw region
      (source.plugLayout.frameRegion source.site) path),
    route.HasCutDepth depth → depthAllowed siteDirection direction depth

/-- At the distinguished site itself, admissibility forces the active
direction to be the citation's focused direction: the reflexive route has cut
depth zero. -/
theorem allowed_at_site_direction_eq
    (presentation : TwoInputPresentation source target)
    (siteDirection direction : ConcreteElaboration.SimulationDirection)
    (allowed : presentation.Allowed siteDirection direction
      (source.plugLayout.frameRegion source.site)) :
    direction = siteDirection := by
  let route : RegionRoute source.plugLayout.plugRaw
      (source.plugLayout.frameRegion source.site)
      (source.plugLayout.frameRegion source.site) [] :=
    RegionRoute.here (d := source.plugLayout.plugRaw)
      (source.plugLayout.frameRegion source.site)
  have routeDepth : route.HasCutDepth 0 := by
    exact RegionRoute.HasCutDepth.here (d := source.plugLayout.plugRaw)
      (source.plugLayout.frameRegion source.site)
  have parity : depthAllowed siteDirection direction 0 :=
    allowed route routeDepth
  cases siteDirection <;> cases direction <;>
    simp [depthAllowed] at parity ⊢

theorem allowed_cut
    (presentation : TwoInputPresentation source target)
    (siteDirection direction : ConcreteElaboration.SimulationDirection)
    (child parent : Fin source.plugLayout.plugRaw.regionCount)
    (childKind : source.plugLayout.plugRaw.regions child = .cut parent)
    (allowed : presentation.Allowed siteDirection direction parent) :
    presentation.Allowed siteDirection direction.flip child := by
  intro path depth route routeDepth
  have childParent :
      (source.plugLayout.plugRaw.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, hposition⟩ := VisualProof.Data.Finite.indexOf?_complete
    ((ConcreteElaboration.mem_localOccurrences_child
      source.plugLayout.plugRaw parent child).2 childParent)
  let parentRoute := RegionRoute.step childParent position hposition route
  have parentDepth : parentRoute.HasCutDepth (depth + 1) := by
    exact RegionRoute.HasCutDepth.cut
      (hparent := childParent) (position := position)
      (hposition := hposition) childKind routeDepth
  have parity := allowed parentRoute parentDepth
  cases siteDirection <;> cases direction <;>
    simp [depthAllowed] at parity ⊢ <;> omega

theorem allowed_bubble
    (presentation : TwoInputPresentation source target)
    (siteDirection direction : ConcreteElaboration.SimulationDirection)
    (child parent : Fin source.plugLayout.plugRaw.regionCount)
    (arity : Nat)
    (childKind : source.plugLayout.plugRaw.regions child =
      .bubble parent arity)
    (allowed : presentation.Allowed siteDirection direction parent) :
    presentation.Allowed siteDirection direction child := by
  intro path depth route routeDepth
  have childParent :
      (source.plugLayout.plugRaw.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, hposition⟩ := VisualProof.Data.Finite.indexOf?_complete
    ((ConcreteElaboration.mem_localOccurrences_child
      source.plugLayout.plugRaw parent child).2 childParent)
  let parentRoute := RegionRoute.step childParent position hposition route
  have parentDepth : parentRoute.HasCutDepth depth := by
    exact RegionRoute.HasCutDepth.bubble
      (hparent := childParent) (position := position)
      (hposition := hposition) childKind routeDepth
  exact allowed parentRoute parentDepth

/-- Concrete provenance for every pair of compiler contexts reached by the
shared two-input traversal.  Focused extension is retained separately so the
kernel can recurse only into children that are direct children on both sides. -/
inductive ContextWitness
    (presentation : TwoInputPresentation source target)
    (sourceBoundary : List (Fin source.frame.val.wireCount)) :
    ConcreteElaboration.WireContext source.plugLayout.plugRaw →
      ConcreteElaboration.WireContext target.plugLayout.plugRaw → Type
  | root :
      ContextWitness presentation sourceBoundary
        (PlugLayout.outputOpenRoot source source.plugLayout
          sourceBoundary).rootWires
        (PlugLayout.outputOpenRoot target target.plugLayout
          (presentation.targetBoundary sourceBoundary)).rootWires
  | extendRegular
      {sourceContext : ConcreteElaboration.WireContext
        source.plugLayout.plugRaw}
      {targetContext : ConcreteElaboration.WireContext
        target.plugLayout.plugRaw}
      (parent : ContextWitness presentation sourceBoundary
        sourceContext targetContext)
      (region : Fin source.plugLayout.plugRaw.regionCount)
      (regular : ¬ presentation.Distinguished region)
      (sourceExact : (sourceContext.extend region).Exact region)
      (targetExact :
        (targetContext.extend (presentation.regionMap region)).Exact
          (presentation.regionMap region)) :
      ContextWitness presentation sourceBoundary
        (sourceContext.extend region)
        (targetContext.extend (presentation.regionMap region))
  | extendFocused
      {sourceContext : ConcreteElaboration.WireContext
        source.plugLayout.plugRaw}
      {targetContext : ConcreteElaboration.WireContext
        target.plugLayout.plugRaw}
      (parent : ContextWitness presentation sourceBoundary
        sourceContext targetContext)
      (region : Fin source.plugLayout.plugRaw.regionCount)
      (focused : presentation.Distinguished region)
      (sourceExact : (sourceContext.extend region).Exact region)
      (targetExact :
        (targetContext.extend (presentation.regionMap region)).Exact
          (presentation.regionMap region)) :
      ContextWitness presentation sourceBoundary
        (sourceContext.extend region)
        (targetContext.extend (presentation.regionMap region))

/-- The exact compiler route represented by a paired context witness.  Root
compilation starts at the root; recursive compilation reaches only actual
direct children of a regular region whose context was just extended. -/
inductive ContextWitness.AtRegion
    {presentation : TwoInputPresentation source target}
    {sourceBoundary : List (Fin source.frame.val.wireCount)} :
    {sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw} →
    {targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw} →
    (witness : ContextWitness presentation sourceBoundary
      sourceContext targetContext) →
    Fin source.plugLayout.plugRaw.regionCount → Prop
  | root :
      AtRegion (.root (presentation := presentation)
        (sourceBoundary := sourceBoundary))
        source.plugLayout.plugRaw.root
  | rootChild
      (regular :
        ¬ presentation.Distinguished source.plugLayout.plugRaw.root)
      {child : Fin source.plugLayout.plugRaw.regionCount}
      (parent :
        (source.plugLayout.plugRaw.regions child).parent? =
          some source.plugLayout.plugRaw.root) :
      AtRegion (.root (presentation := presentation)
        (sourceBoundary := sourceBoundary)) child
  | rootFocusedChild
      (focused :
        presentation.Distinguished source.plugLayout.plugRaw.root)
      {child : Fin source.plugLayout.plugRaw.regionCount}
      (sourceParent :
        (source.plugLayout.plugRaw.regions child).parent? =
          some source.plugLayout.plugRaw.root)
      (targetParent :
        (target.plugLayout.plugRaw.regions
          (presentation.regionMap child)).parent? =
            some (presentation.regionMap source.plugLayout.plugRaw.root)) :
      AtRegion (.root (presentation := presentation)
        (sourceBoundary := sourceBoundary)) child
  | extendChild
      {sourceContext : ConcreteElaboration.WireContext
        source.plugLayout.plugRaw}
      {targetContext : ConcreteElaboration.WireContext
        target.plugLayout.plugRaw}
      {parent : Fin source.plugLayout.plugRaw.regionCount}
      {parentWitness : ContextWitness presentation sourceBoundary
        sourceContext targetContext}
      (parentAt : AtRegion parentWitness parent)
      (regular : ¬ presentation.Distinguished parent)
      (sourceExact : (sourceContext.extend parent).Exact parent)
      (targetExact :
        (targetContext.extend (presentation.regionMap parent)).Exact
          (presentation.regionMap parent))
      {child : Fin source.plugLayout.plugRaw.regionCount}
      (childParent :
        (source.plugLayout.plugRaw.regions child).parent? = some parent) :
      AtRegion
        (.extendRegular parentWitness parent regular sourceExact targetExact)
        child
  | extendHere
      {sourceContext : ConcreteElaboration.WireContext
        source.plugLayout.plugRaw}
      {targetContext : ConcreteElaboration.WireContext
        target.plugLayout.plugRaw}
      {region : Fin source.plugLayout.plugRaw.regionCount}
      {parentWitness : ContextWitness presentation sourceBoundary
        sourceContext targetContext}
      (atRegion : AtRegion parentWitness region)
      (regular : ¬ presentation.Distinguished region)
      (sourceExact : (sourceContext.extend region).Exact region)
      (targetExact :
        (targetContext.extend (presentation.regionMap region)).Exact
          (presentation.regionMap region)) :
      AtRegion
        (.extendRegular parentWitness region regular sourceExact targetExact)
        region
  | extendFocusedChild
      {sourceContext : ConcreteElaboration.WireContext
        source.plugLayout.plugRaw}
      {targetContext : ConcreteElaboration.WireContext
        target.plugLayout.plugRaw}
      {parent : Fin source.plugLayout.plugRaw.regionCount}
      {parentWitness : ContextWitness presentation sourceBoundary
        sourceContext targetContext}
      (parentAt : AtRegion parentWitness parent)
      (focused : presentation.Distinguished parent)
      (sourceExact : (sourceContext.extend parent).Exact parent)
      (targetExact :
        (targetContext.extend (presentation.regionMap parent)).Exact
          (presentation.regionMap parent))
      {child : Fin source.plugLayout.plugRaw.regionCount}
      (sourceParent :
        (source.plugLayout.plugRaw.regions child).parent? = some parent)
      (targetParent :
        (target.plugLayout.plugRaw.regions
          (presentation.regionMap child)).parent? =
            some (presentation.regionMap parent)) :
      AtRegion
        (.extendFocused parentWitness parent focused sourceExact targetExact)
        child

/-- Every distinguished region reached by the actual shared compiler route is
the retained splice site.  Source-pattern material is distinguished only to
make the total structural presentation possible; the compiler never enters it
because it stops at the site. -/
theorem ContextWitness.focused_region_eq_site
    {presentation : TwoInputPresentation source target}
    {sourceBoundary : List (Fin source.frame.val.wireCount)}
    {sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw}
    {targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw}
    {witness : ContextWitness presentation sourceBoundary
      sourceContext targetContext}
    {region : Fin source.plugLayout.plugRaw.regionCount}
    (atRegion : ContextWitness.AtRegion witness region)
    (focused : presentation.Distinguished region) :
    region = source.plugLayout.frameRegion source.site := by
  induction atRegion with
  | root =>
      rcases focused with focused | ⟨material, focused⟩
      · exact focused
      · exact False.elim
          (source.plugLayout.frameRegion_ne_materialRegion
            source.frame.val.root material focused)
  | rootChild regular parent =>
      obtain ⟨frame, rfl⟩ :=
        presentation.regularChildFrameRegion
          source.plugLayout.plugRaw.root _ regular parent
      rcases focused with focused | ⟨material, focused⟩
      · exact focused
      · exact False.elim
          (source.plugLayout.frameRegion_ne_materialRegion frame material focused)
  | @rootFocusedChild rootFocused child sourceParent targetParent =>
      have rootEq :
          source.plugLayout.plugRaw.root =
            source.plugLayout.frameRegion source.site := by
        rcases rootFocused with rootFocused | ⟨material, rootFocused⟩
        · exact rootFocused
        · exact False.elim
            (source.plugLayout.frameRegion_ne_materialRegion
              source.frame.val.root material rootFocused)
      have childMapEq :
          presentation.regionMap child =
            target.plugLayout.frameRegion target.site := by
        rcases focused with childFocused | ⟨material, childFocused⟩
        · exact (congrArg presentation.regionMap childFocused).trans
            presentation.regionMap_site
        · exact (congrArg presentation.regionMap childFocused).trans (by
            simp [regionMap, PlugLayout.materialRegion,
              PlugLayout.plugRaw, PlugLayout.regionCount])
      have rootMapEq :
          presentation.regionMap source.plugLayout.plugRaw.root =
            target.plugLayout.frameRegion target.site := by
        rw [rootEq, presentation.regionMap_site]
      rw [childMapEq, rootMapEq] at targetParent
      have targetMember :
          ConcreteElaboration.LocalOccurrence.child
              (target.plugLayout.frameRegion target.site) ∈
            ConcreteElaboration.localOccurrences target.plugLayout.plugRaw
              (target.plugLayout.frameRegion target.site) :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).2 targetParent
      have rawMember :
          ConcreteElaboration.LocalOccurrence.child target.site ∈
            ConcreteElaboration.localOccurrences target.coalesceFrameRaw
              target.site :=
        (target.plugLayout.mapFrameOccurrence_mem_localOccurrences target.site
          (.child target.site)).1 targetMember
      have rawParent :
          (target.frame.val.regions target.site).parent? =
            some target.site := by
        exact (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 rawMember
      exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent
          target.frame.property rawParent
          (ConcreteDiagram.Encloses.refl target.frame.val target.site))
  | extendChild parentAt regular sourceExact targetExact childParent =>
      obtain ⟨frame, rfl⟩ :=
        presentation.regularChildFrameRegion _ _ regular childParent
      rcases focused with focused | ⟨material, focused⟩
      · exact focused
      · exact False.elim
          (source.plugLayout.frameRegion_ne_materialRegion frame material focused)
  | extendHere atRegion regular sourceExact targetExact ih =>
      exact False.elim (regular focused)
  | @extendFocusedChild sourceContext targetContext parent parentWitness
      parentAt parentFocused sourceExact targetExact child sourceParent
      targetParent ih =>
      have parentEq := ih parentFocused
      have childMapEq :
          presentation.regionMap child =
            target.plugLayout.frameRegion target.site := by
        rcases focused with childFocused | ⟨material, childFocused⟩
        · exact (congrArg presentation.regionMap childFocused).trans
            presentation.regionMap_site
        · exact (congrArg presentation.regionMap childFocused).trans (by
            simp [regionMap, PlugLayout.materialRegion,
              PlugLayout.plugRaw, PlugLayout.regionCount])
      rw [childMapEq, parentEq, presentation.regionMap_site] at targetParent
      have targetMember :
          ConcreteElaboration.LocalOccurrence.child
              (target.plugLayout.frameRegion target.site) ∈
            ConcreteElaboration.localOccurrences target.plugLayout.plugRaw
              (target.plugLayout.frameRegion target.site) :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).2 targetParent
      have rawMember :
          ConcreteElaboration.LocalOccurrence.child target.site ∈
            ConcreteElaboration.localOccurrences target.coalesceFrameRaw
              target.site :=
        (target.plugLayout.mapFrameOccurrence_mem_localOccurrences target.site
          (.child target.site)).1 targetMember
      have rawParent :
          (target.frame.val.regions target.site).parent? =
            some target.site := by
        exact (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 rawMember
      exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent
          target.frame.property rawParent
          (ConcreteDiagram.Encloses.refl target.frame.val target.site))

/-- Relate compiler-context indices exactly when both carry the plug-layout
copies of quotient classes containing one shared retained-frame wire.  This is
many-to-many and therefore does not choose a refinement direction between the
two boundary partitions. -/
def contextIndexRelation
    (presentation : TwoInputPresentation source target)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length where
  Rel sourceIndex targetIndex :=
    ∃ wire : Fin source.frame.val.wireCount,
      sourceContext.get sourceIndex = source.plugLayout.frameWire
          (source.quotientWire wire) ∧
        targetContext.get targetIndex = target.plugLayout.frameWire
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire))

/-- On complete nested root contexts, shared-wire provenance is exactly the
graph of the canonical root-wire equivalence. -/
theorem contextIndexRelation_root_iff_of_nested
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (sourceIndex : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).rootWires.length)
    (targetIndex : Fin (PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)).rootWires.length) :
    (presentation.contextIndexRelation
      (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).rootWires
      (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).rootWires).Rel
        sourceIndex targetIndex ↔
      presentation.outputRootWireEquivOfNested sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested sourceIndex =
          targetIndex := by
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let rootEquiv :=
    presentation.outputRootWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  constructor
  · rintro ⟨wire, sourceGet, targetGet⟩
    obtain ⟨mappedWire, mappedSourceGet, mappedTargetGet⟩ :=
      presentation.outputRootWireEquivOfNested_related sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested sourceIndex
    have sourceClasses :
        source.quotientWire wire = source.quotientWire mappedWire :=
      source.plugLayout.frameWire_injective
        (sourceGet.symm.trans mappedSourceGet)
    have sourceScope :
        source.coalescedScope (source.quotientWire wire) =
          source.frame.val.root := by
      have frameMem :
          source.plugLayout.frameWire (source.quotientWire wire) ∈
            sourceOpen.rootWires :=
        sourceGet ▸ List.get_mem sourceOpen.rootWires sourceIndex
      have quotientMem :
          source.quotientWire wire ∈
            (PlugLayout.coalescedOpenRoot source
              sourceBoundary).rootWires := by
        change source.plugLayout.frameWire (source.quotientWire wire) ∈
            sourceOpen.exposedWires ++ sourceOpen.hiddenWires at frameMem
        change source.quotientWire wire ∈
          (PlugLayout.coalescedOpenRoot source
              sourceBoundary).exposedWires ++
            (PlugLayout.coalescedOpenRoot source
              sourceBoundary).hiddenWires
        rcases List.mem_append.mp frameMem with exposed | hidden
        · exact List.mem_append.mpr <| .inl <|
            (PlugLayout.frameWire_mem_rootExposed_iff source
              source.plugLayout sourceBoundary
              (source.quotientWire wire)).1 exposed
        · exact List.mem_append.mpr <| .inr <|
            (PlugLayout.frameWire_mem_rootHidden_iff_of_nested source
              source.plugLayout sourceBoundary hnested
              (source.quotientWire wire)).1 hidden
      have quotientScoped :=
        (OpenConcreteDiagram.mem_rootWires_iff
          (PlugLayout.coalescedOpenRoot source sourceBoundary)
          (PlugLayout.coalescedOpenRoot_wellFormed source sourceAdmissible
            sourceBoundary sourceRoot)
          (source.quotientWire wire)).1 quotientMem
      simpa [PlugLayout.coalescedOpenRoot] using quotientScoped
    have mappedScope :
        source.coalescedScope (source.quotientWire mappedWire) =
          source.frame.val.root := by
      rw [← sourceClasses]
      exact sourceScope
    have targetClasses :
        target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire) =
          target.quotientWire
            (Fin.cast presentation.frameWireCountEq mappedWire) := by
      calc
        _ = presentation.quotientMap (source.quotientWire wire) := by
          symm
          exact presentation.quotientMap_quotientWire_of_coalescedScope
            source.frame.val.root (fun equality => hnested equality.symm)
            wire sourceScope
        _ = presentation.quotientMap
            (source.quotientWire mappedWire) :=
          congrArg presentation.quotientMap sourceClasses
        _ = _ := presentation.quotientMap_quotientWire_of_coalescedScope
          source.frame.val.root (fun equality => hnested equality.symm)
          mappedWire mappedScope
    apply Fin.ext
    apply (List.getElem_inj targetOpen.rootWires_nodup).mp
    simpa only [List.get_eq_getElem, rootEquiv] using
      mappedTargetGet.trans
        ((congrArg target.plugLayout.frameWire targetClasses.symm).trans
          targetGet.symm)
  · intro indexEq
    obtain ⟨wire, sourceGet, targetGet⟩ :=
      presentation.outputRootWireEquivOfNested_related sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested sourceIndex
    subst targetIndex
    exact ⟨wire, sourceGet, targetGet⟩

/-- Canonical injections of the exposed and hidden blocks into the complete
root context. -/
def rootExposedIndex (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.exposedWires.length) :
    Fin openDiagram.rootWires.length :=
  Fin.cast (by simp [OpenConcreteDiagram.rootWires])
    (Fin.castAdd openDiagram.hiddenWires.length index)

def rootHiddenIndex (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.hiddenWires.length) :
    Fin openDiagram.rootWires.length :=
  Fin.cast (by simp [OpenConcreteDiagram.rootWires])
    (Fin.natAdd openDiagram.exposedWires.length index)

@[simp] theorem rootEnvironment_rootExposedIndex
    (openDiagram : OpenConcreteDiagram)
    (outer : Fin openDiagram.exposedWires.length → D)
    (localEnv : Fin openDiagram.hiddenWires.length → D)
    (index : Fin openDiagram.exposedWires.length) :
    ConcreteElaboration.rootEnvironment openDiagram.exposedWires
        openDiagram.hiddenWires outer localEnv
        (rootExposedIndex openDiagram index) =
      outer index := by
  unfold ConcreteElaboration.rootEnvironment
  let lengthEq : openDiagram.rootWires.length =
      openDiagram.exposedWires.length + openDiagram.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  change Fin.addCases outer localEnv
      (Fin.cast lengthEq (rootExposedIndex openDiagram index)) =
    outer index
  have indexEq :
      Fin.cast lengthEq (rootExposedIndex openDiagram index) =
        Fin.castAdd openDiagram.hiddenWires.length index := by
    apply Fin.ext
    rfl
  rw [indexEq]
  exact Fin.addCases_left index

@[simp] theorem rootEnvironment_rootHiddenIndex
    (openDiagram : OpenConcreteDiagram)
    (outer : Fin openDiagram.exposedWires.length → D)
    (localEnv : Fin openDiagram.hiddenWires.length → D)
    (index : Fin openDiagram.hiddenWires.length) :
    ConcreteElaboration.rootEnvironment openDiagram.exposedWires
        openDiagram.hiddenWires outer localEnv
        (rootHiddenIndex openDiagram index) =
      localEnv index := by
  unfold ConcreteElaboration.rootEnvironment
  let lengthEq : openDiagram.rootWires.length =
      openDiagram.exposedWires.length + openDiagram.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  change Fin.addCases outer localEnv
      (Fin.cast lengthEq (rootHiddenIndex openDiagram index)) =
    localEnv index
  have indexEq :
      Fin.cast lengthEq (rootHiddenIndex openDiagram index) =
        Fin.natAdd openDiagram.exposedWires.length index := by
    apply Fin.ext
    rfl
  rw [indexEq]
  exact Fin.addCases_right index

/-- Splitting a complete root valuation into its exposed and hidden blocks
and recombining them recovers the original compiler-order valuation. -/
theorem rootEnvironment_of_complete
    (openDiagram : OpenConcreteDiagram)
    (env : Fin openDiagram.rootWires.length → D) :
    ConcreteElaboration.rootEnvironment openDiagram.exposedWires
        openDiagram.hiddenWires
        (fun index => env (rootExposedIndex openDiagram index))
        (fun index => env (rootHiddenIndex openDiagram index)) =
      env := by
  funext index
  let lengthEq : openDiagram.rootWires.length =
      openDiagram.exposedWires.length + openDiagram.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let split := Fin.cast lengthEq index
  have recover : Fin.cast lengthEq.symm split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  · simpa [rootExposedIndex] using
      rootEnvironment_rootExposedIndex openDiagram
        (fun index => env (rootExposedIndex openDiagram index))
        (fun index => env (rootHiddenIndex openDiagram index)) exposed
  · simpa [rootHiddenIndex] using
      rootEnvironment_rootHiddenIndex openDiagram
        (fun index => env (rootExposedIndex openDiagram index))
        (fun index => env (rootHiddenIndex openDiagram index)) hidden

theorem outputRootWireEquivOfNested_rootExposedIndex
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (index : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).exposedWires.length) :
    presentation.outputRootWireEquivOfNested sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested
        (rootExposedIndex
          (PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary)
          index) =
      rootExposedIndex
        (PlugLayout.outputOpenRoot target target.plugLayout
          (presentation.targetBoundary sourceBoundary))
        (presentation.outputRootExposedWireEquivOfNested sourceAdmissible
          targetAdmissible sourceBoundary sourceRoot hnested index) := by
  simp [rootExposedIndex, outputRootWireEquivOfNested,
    FiniteEquiv.finCast, extendWireEquiv]

theorem outputRootWireEquivOfNested_rootHiddenIndex
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (index : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).hiddenWires.length) :
    presentation.outputRootWireEquivOfNested sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested
        (rootHiddenIndex
          (PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary)
          index) =
      rootHiddenIndex
        (PlugLayout.outputOpenRoot target target.plugLayout
          (presentation.targetBoundary sourceBoundary))
        (presentation.outputRootHiddenWireEquivOfNested sourceAdmissible
          targetAdmissible sourceBoundary sourceRoot hnested index) := by
  simp [rootHiddenIndex, outputRootWireEquivOfNested,
    FiniteEquiv.finCast, extendWireEquiv]

/-- A valuation of the source hidden root block extends any agreeing exposed
valuation to the complete paired nested root contexts. -/
theorem nestedRootForwardSelection
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (sourceOuter : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).exposedWires.length → D)
    (targetOuter : Fin (PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)).exposedWires.length → D)
    (outerAgrees :
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (presentation.outputRootExposedWireEquivOfNested sourceAdmissible
          targetAdmissible sourceBoundary sourceRoot hnested)).EnvironmentsAgree
            sourceOuter targetOuter)
    (sourceLocal : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).hiddenWires.length → D) :
    ∃ targetLocal : Fin (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).hiddenWires.length → D,
      (presentation.contextIndexRelation
        (PlugLayout.outputOpenRoot source source.plugLayout
          sourceBoundary).rootWires
        (PlugLayout.outputOpenRoot target target.plugLayout
          (presentation.targetBoundary sourceBoundary)).rootWires
      ).EnvironmentsAgree
        (ConcreteElaboration.rootEnvironment
          (PlugLayout.outputOpenRoot source source.plugLayout
            sourceBoundary).exposedWires
          (PlugLayout.outputOpenRoot source source.plugLayout
            sourceBoundary).hiddenWires sourceOuter sourceLocal)
        (ConcreteElaboration.rootEnvironment
          (PlugLayout.outputOpenRoot target target.plugLayout
            (presentation.targetBoundary sourceBoundary)).exposedWires
          (PlugLayout.outputOpenRoot target target.plugLayout
            (presentation.targetBoundary sourceBoundary)).hiddenWires
          targetOuter targetLocal) := by
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let exposedEquiv :=
    presentation.outputRootExposedWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  let hiddenEquiv :=
    presentation.outputRootHiddenWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  let rootEquiv :=
    presentation.outputRootWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  let targetLocal : Fin targetOpen.hiddenWires.length → D :=
    sourceLocal ∘ hiddenEquiv.symm
  refine ⟨targetLocal, ?_⟩
  intro sourceIndex targetIndex related
  have mapped :
      rootEquiv sourceIndex = targetIndex := by
    exact (presentation.contextIndexRelation_root_iff_of_nested
      sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
      sourceIndex targetIndex).1 related
  subst targetIndex
  let sourceEq : sourceOpen.rootWires.length =
      sourceOpen.exposedWires.length + sourceOpen.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let split := Fin.cast sourceEq sourceIndex
  have sourceIndexEq :
      sourceIndex = Fin.cast sourceEq.symm split := by
    apply Fin.ext
    rfl
  rw [sourceIndexEq]
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  · have agrees := outerAgrees exposed (exposedEquiv exposed) rfl
    have indexForm :
        Fin.cast sourceEq.symm
            (Fin.castAdd sourceOpen.hiddenWires.length exposed) =
          rootExposedIndex sourceOpen exposed := by
      apply Fin.ext
      rfl
    rw [indexForm]
    rw [show rootEquiv (rootExposedIndex sourceOpen exposed) =
        rootExposedIndex targetOpen (exposedEquiv exposed) by
      simpa [sourceOpen, targetOpen, exposedEquiv, rootEquiv] using
        presentation.outputRootWireEquivOfNested_rootExposedIndex
          sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
          exposed]
    simpa [sourceOpen, targetOpen] using agrees
  · have indexForm :
        Fin.cast sourceEq.symm
            (Fin.natAdd sourceOpen.exposedWires.length hidden) =
          rootHiddenIndex sourceOpen hidden := by
      apply Fin.ext
      rfl
    rw [indexForm]
    rw [show rootEquiv (rootHiddenIndex sourceOpen hidden) =
        rootHiddenIndex targetOpen (hiddenEquiv hidden) by
      simpa [sourceOpen, targetOpen, hiddenEquiv, rootEquiv] using
        presentation.outputRootWireEquivOfNested_rootHiddenIndex
          sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
          hidden]
    rw [rootEnvironment_rootHiddenIndex, rootEnvironment_rootHiddenIndex]
    change sourceLocal hidden =
      sourceLocal (hiddenEquiv.symm (hiddenEquiv hidden))
    exact congrArg sourceLocal
      (FiniteEquiv.symm_apply_apply hiddenEquiv hidden).symm

/-- The backward dual reconstructs the source hidden valuation from the
target hidden block while preserving the same exposed-context agreement. -/
theorem nestedRootBackwardSelection
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (sourceOuter : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).exposedWires.length → D)
    (targetOuter : Fin (PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)).exposedWires.length → D)
    (outerAgrees :
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (presentation.outputRootExposedWireEquivOfNested sourceAdmissible
          targetAdmissible sourceBoundary sourceRoot hnested)).EnvironmentsAgree
            sourceOuter targetOuter)
    (targetLocal : Fin (PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)).hiddenWires.length → D) :
    ∃ sourceLocal : Fin (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).hiddenWires.length → D,
      (presentation.contextIndexRelation
        (PlugLayout.outputOpenRoot source source.plugLayout
          sourceBoundary).rootWires
        (PlugLayout.outputOpenRoot target target.plugLayout
          (presentation.targetBoundary sourceBoundary)).rootWires
      ).EnvironmentsAgree
        (ConcreteElaboration.rootEnvironment
          (PlugLayout.outputOpenRoot source source.plugLayout
            sourceBoundary).exposedWires
          (PlugLayout.outputOpenRoot source source.plugLayout
            sourceBoundary).hiddenWires sourceOuter sourceLocal)
        (ConcreteElaboration.rootEnvironment
          (PlugLayout.outputOpenRoot target target.plugLayout
            (presentation.targetBoundary sourceBoundary)).exposedWires
          (PlugLayout.outputOpenRoot target target.plugLayout
            (presentation.targetBoundary sourceBoundary)).hiddenWires
          targetOuter targetLocal) := by
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let exposedEquiv :=
    presentation.outputRootExposedWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  let hiddenEquiv :=
    presentation.outputRootHiddenWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  let rootEquiv :=
    presentation.outputRootWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested
  let sourceLocal : Fin sourceOpen.hiddenWires.length → D :=
    targetLocal ∘ hiddenEquiv
  refine ⟨sourceLocal, ?_⟩
  intro sourceIndex targetIndex related
  have mapped :
      rootEquiv sourceIndex = targetIndex := by
    exact (presentation.contextIndexRelation_root_iff_of_nested
      sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
      sourceIndex targetIndex).1 related
  subst targetIndex
  let sourceEq : sourceOpen.rootWires.length =
      sourceOpen.exposedWires.length + sourceOpen.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let split := Fin.cast sourceEq sourceIndex
  have sourceIndexEq :
      sourceIndex = Fin.cast sourceEq.symm split := by
    apply Fin.ext
    rfl
  rw [sourceIndexEq]
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  · have agrees := outerAgrees exposed (exposedEquiv exposed) rfl
    have indexForm :
        Fin.cast sourceEq.symm
            (Fin.castAdd sourceOpen.hiddenWires.length exposed) =
          rootExposedIndex sourceOpen exposed := by
      apply Fin.ext
      rfl
    rw [indexForm]
    rw [show rootEquiv (rootExposedIndex sourceOpen exposed) =
        rootExposedIndex targetOpen (exposedEquiv exposed) by
      simpa [sourceOpen, targetOpen, exposedEquiv, rootEquiv] using
        presentation.outputRootWireEquivOfNested_rootExposedIndex
          sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
          exposed]
    simpa [sourceOpen, targetOpen] using agrees
  · have indexForm :
        Fin.cast sourceEq.symm
            (Fin.natAdd sourceOpen.exposedWires.length hidden) =
          rootHiddenIndex sourceOpen hidden := by
      apply Fin.ext
      rfl
    rw [indexForm]
    rw [show rootEquiv (rootHiddenIndex sourceOpen hidden) =
        rootHiddenIndex targetOpen (hiddenEquiv hidden) by
      simpa [sourceOpen, targetOpen, hiddenEquiv, rootEquiv] using
        presentation.outputRootWireEquivOfNested_rootHiddenIndex
          sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
          hidden]
    simp [sourceOpen, targetOpen, sourceLocal, hiddenEquiv]

theorem contextIndexRelation_of_sharedWire
    (presentation : TwoInputPresentation source target)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (wire : Fin source.frame.val.wireCount)
    (sourceWire : sourceContext.get sourceIndex =
      source.plugLayout.frameWire (source.quotientWire wire))
    (targetWire : targetContext.get targetIndex =
      target.plugLayout.frameWire
        (target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire))) :
    (presentation.contextIndexRelation sourceContext targetContext).Rel
      sourceIndex targetIndex := by
  exact ⟨wire, sourceWire, targetWire⟩

/-- Reordering either exact compiler context by wire-preserving finite
equivalences preserves the paired retained-wire environment relation. -/
theorem contextIndexRelation_environmentsAgree_reindex
    (presentation : TwoInputPresentation source target)
    (sourceContext sourceContext' :
      ConcreteElaboration.WireContext source.plugLayout.plugRaw)
    (targetContext targetContext' :
      ConcreteElaboration.WireContext target.plugLayout.plugRaw)
    (sourceEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin sourceContext'.length))
    (targetEquiv : FiniteEquiv (Fin targetContext.length)
      (Fin targetContext'.length))
    (sourceSpec : ∀ index,
      sourceContext'.get (sourceEquiv index) = sourceContext.get index)
    (targetSpec : ∀ index,
      targetContext'.get (targetEquiv index) = targetContext.get index)
    (sourceEnv : Fin sourceContext.length → D)
    (targetEnv : Fin targetContext.length → D)
    (agrees :
      (presentation.contextIndexRelation sourceContext targetContext
        ).EnvironmentsAgree sourceEnv targetEnv) :
    (presentation.contextIndexRelation sourceContext' targetContext'
      ).EnvironmentsAgree
        (sourceEnv ∘ sourceEquiv.symm)
        (targetEnv ∘ targetEquiv.symm) := by
  intro sourceIndex targetIndex related
  obtain ⟨wire, sourceWire, targetWire⟩ := related
  let sourceOriginal := sourceEquiv.symm sourceIndex
  let targetOriginal := targetEquiv.symm targetIndex
  have sourceIndexEq : sourceEquiv sourceOriginal = sourceIndex :=
    sourceEquiv.right_inv sourceIndex
  have targetIndexEq : targetEquiv targetOriginal = targetIndex :=
    targetEquiv.right_inv targetIndex
  apply agrees sourceOriginal targetOriginal
  refine ⟨wire, ?_, ?_⟩
  · rw [← sourceSpec sourceOriginal, sourceIndexEq]
    exact sourceWire
  · rw [← targetSpec targetOriginal, targetIndexEq]
    exact targetWire

/-- Resolving the same port of corresponding retained-frame nodes produces
indices related by the shared original-wire provenance relation. -/
theorem contextIndexRelation_of_resolved_frame_port
    (presentation : TwoInputPresentation source target)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (node : Fin source.frame.val.nodeCount)
    (port : CPort)
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (sourceResolved :
      ConcreteElaboration.resolvePort? source.plugLayout.plugRaw sourceContext
        (source.plugLayout.frameNode node) port = some sourceIndex)
    (targetResolved :
      ConcreteElaboration.resolvePort? target.plugLayout.plugRaw targetContext
        (target.plugLayout.frameNode
          (Fin.cast presentation.frameNodeCountEq node)) port =
        some targetIndex) :
    (presentation.contextIndexRelation sourceContext targetContext).Rel
      sourceIndex targetIndex := by
  obtain ⟨sourcePlugWire, sourceOccurs, sourceGet⟩ :=
    ConcreteElaboration.resolvePort?_sound sourceResolved
  obtain ⟨targetPlugWire, targetOccurs, targetGet⟩ :=
    ConcreteElaboration.resolvePort?_sound targetResolved
  obtain ⟨sourceClass, sourceClassWire, sourceClassOccurs⟩ :=
    source.plugLayout.plugRaw_frameEndpoint_backward sourcePlugWire
      ⟨node, port⟩ (by
        simpa [PlugLayout.mapFrameEndpoint] using sourceOccurs)
  obtain ⟨targetClass, targetClassWire, targetClassOccurs⟩ :=
    target.plugLayout.plugRaw_frameEndpoint_backward targetPlugWire
      ⟨Fin.cast presentation.frameNodeCountEq node, port⟩ (by
        simpa [PlugLayout.mapFrameEndpoint] using targetOccurs)
  change ⟨node, port⟩ ∈ source.coalescedEndpoints sourceClass
    at sourceClassOccurs
  rw [source.mem_coalescedEndpoints] at sourceClassOccurs
  obtain ⟨sourceWire, sourceWireClass, sourceWireOccurs⟩ :=
    sourceClassOccurs
  change
    ⟨Fin.cast presentation.frameNodeCountEq node, port⟩ ∈
      target.coalescedEndpoints targetClass at targetClassOccurs
  rw [target.mem_coalescedEndpoints] at targetClassOccurs
  obtain ⟨targetWire, targetWireClass, targetWireOccurs⟩ :=
    targetClassOccurs
  have transportedSourceOccurs :
      target.frame.val.EndpointOccurs
        (Fin.cast presentation.frameWireCountEq sourceWire)
        ⟨Fin.cast presentation.frameNodeCountEq node, port⟩ :=
    (checkedDiagram_endpointOccurs_eq source.frame target.frame
      presentation.frame_eq sourceWire ⟨node, port⟩).1 sourceWireOccurs
  have targetWireEq :
      targetWire = Fin.cast presentation.frameWireCountEq sourceWire :=
    checked_endpoint_wire_unique target.frame targetWire
      (Fin.cast presentation.frameWireCountEq sourceWire)
      ⟨Fin.cast presentation.frameNodeCountEq node, port⟩
      targetWireOccurs transportedSourceOccurs
  refine presentation.contextIndexRelation_of_sharedWire sourceContext
    targetContext sourceIndex targetIndex sourceWire ?_ ?_
  · exact sourceGet.trans (sourceClassWire.symm.trans (congrArg
      source.plugLayout.frameWire
      ((source.mem_classWires sourceClass sourceWire).1 sourceWireClass).symm))
  · exact targetGet.trans (targetClassWire.symm.trans (congrArg
      target.plugLayout.frameWire
      (((target.mem_classWires targetClass targetWire).1 targetWireClass).symm
        |>.trans (congrArg target.quotientWire targetWireEq))))

/-- One retained-frame occurrence at the focused site is semantically
transported by the actual source and target compiler calls.  Nodes use shared
port provenance; child wrappers use only their retained-frame shape and the
authoritative recursive callback supplied by the compiler traversal. -/
theorem focusedFrameOccurrence_itemSimulation_of_compiled
    {signature : List Nat} {source target : Input signature}
    {rels : Theory.RelCtx}
    (presentation : TwoInputPresentation source target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (siteDirection direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      source.plugLayout.plugRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.plugLayout.plugRaw)
    (sourceBinders : ConcreteElaboration.BinderContext
      source.plugLayout.plugRaw rels)
    (targetBinders : ConcreteElaboration.BinderContext
      target.plugLayout.plugRaw rels)
    (allowed : presentation.Allowed siteDirection direction
      (source.plugLayout.frameRegion source.site))
    (bindersRelated :
      presentation.BinderRelated sourceBinders targetBinders)
    (sourceBindersCover :
      sourceBinders.Covers (source.plugLayout.frameRegion source.site))
    (targetBindersCover :
      targetBinders.Covers (target.plugLayout.frameRegion target.site))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw sourceBinders
        (source.plugLayout.frameRegion source.site))
    (targetEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw targetBinders
        (target.plugLayout.frameRegion target.site))
    (recurse : ∀
      {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin source.plugLayout.plugRaw.regionCount}
      {childRels : Theory.RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        source.plugLayout.plugRaw childRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        target.plugLayout.plugRaw childRels}
      {sourceBody : Region signature sourceContext.length childRels}
      {targetBody : Region signature targetContext.length childRels},
      (source.plugLayout.plugRaw.regions child).parent? =
          some (source.plugLayout.frameRegion source.site) →
      (target.plugLayout.plugRaw.regions
        (presentation.regionMap child)).parent? =
          some (target.plugLayout.frameRegion target.site) →
      presentation.Allowed siteDirection childDirection child →
      presentation.BinderRelated childSourceBinders childTargetBinders →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (presentation.regionMap child) →
      ConcreteElaboration.BinderContext.Enumeration
        source.plugLayout.plugRaw childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        target.plugLayout.plugRaw childTargetBinders
        (presentation.regionMap child) →
      ConcreteElaboration.compileRegion? signature source.plugLayout.plugRaw
          fuelSource child sourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature target.plugLayout.plugRaw
          fuelTarget (presentation.regionMap child) targetContext
          childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        (presentation.contextIndexRelation sourceContext targetContext)
        sourceBody targetBody)
    (occurrence : ConcreteElaboration.LocalOccurrence
      source.coalesceFrameRaw.regionCount source.coalesceFrameRaw.nodeCount)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences source.coalesceFrameRaw source.site)
    (sourceItem : Item signature sourceContext.length rels)
    (targetItem : Item signature targetContext.length rels)
    (sourceCompiled :
      ConcreteElaboration.compileOccurrenceWith? signature
        source.plugLayout.plugRaw
        (ConcreteElaboration.compileRegion? signature
          source.plugLayout.plugRaw fuelSource)
        sourceContext sourceBinders
        (source.plugLayout.mapFrameOccurrence occurrence) = some sourceItem)
    (targetCompiled :
      ConcreteElaboration.compileOccurrenceWith? signature
        target.plugLayout.plugRaw
        (ConcreteElaboration.compileRegion? signature
          target.plugLayout.plugRaw fuelTarget)
        targetContext targetBinders
        (target.plugLayout.mapFrameOccurrence
          (castLocalOccurrence source.frame target.frame
            presentation.frameRegionCountEq presentation.frameNodeCountEq
            occurrence)) = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      (presentation.contextIndexRelation sourceContext targetContext)
      sourceItem targetItem := by
  cases occurrence with
  | node node =>
      have sourceNodeCompiled :
          ConcreteElaboration.compileNode? signature
            source.plugLayout.plugRaw sourceContext sourceBinders
            (source.plugLayout.frameNode node) = some sourceItem := by
        simpa [ConcreteElaboration.compileOccurrenceWith?,
          PlugLayout.mapFrameOccurrence] using sourceCompiled
      have targetNodeCompiled :
          ConcreteElaboration.compileNode? signature
            target.plugLayout.plugRaw targetContext targetBinders
            (target.plugLayout.frameNode
              (Fin.cast presentation.frameNodeCountEq node)) =
                some targetItem := by
        simpa [ConcreteElaboration.compileOccurrenceWith?,
          PlugLayout.mapFrameOccurrence, castLocalOccurrence] using
            targetCompiled
      rw [← Item.renameRelations_id sourceItem]
      apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
        (source := source.plugLayout.plugRaw)
        (target := target.plugLayout.plugRaw)
        model named direction sourceContext targetContext
        (presentation.contextIndexRelation sourceContext targetContext)
        sourceBinders targetBinders
        (ConcreteElaboration.identityRelationRenaming rels)
        (source.plugLayout.frameNode node)
        (target.plugLayout.frameNode
          (Fin.cast presentation.frameNodeCountEq node))
        (regionMap := presentation.regionMap)
        (binderMap := presentation.regionMap)
      · rw [presentation.frameNode_shape]
        cases source.plugLayout.plugRaw.nodes
            (source.plugLayout.frameNode node) <;>
          rfl
      · intro port sourceIndex targetIndex sourceResolved targetResolved
        exact presentation.contextIndexRelation_of_resolved_frame_port
          sourceContext targetContext node port sourceIndex targetIndex
          sourceResolved targetResolved
      · intro region binder arity sourceRelation sourceAtom sourceLookup
        change source.plugLayout.plugNode
            (source.plugLayout.frameNode node) = .atom region binder
          at sourceAtom
        rw [source.plugLayout.plugNode_frameNode] at sourceAtom
        cases hnode : source.frame.val.nodes node with
        | term nodeRegion freePorts term =>
            simp [hnode, PlugLayout.mapFrameNode] at sourceAtom
        | atom nodeRegion frameBinder =>
            simp [hnode, PlugLayout.mapFrameNode] at sourceAtom
            obtain ⟨rfl, rfl⟩ := sourceAtom
            simpa [presentation.regionMap_frameRegion,
              ConcreteElaboration.identityRelationRenaming] using
                ((bindersRelated frameBinder).symm.trans sourceLookup)
        | named nodeRegion definition arity =>
            simp [hnode, PlugLayout.mapFrameNode] at sourceAtom
      · exact sourceNodeCompiled
      · exact targetNodeCompiled
  | child frameChild =>
      have sourceChildCompiled :
          ConcreteElaboration.compileOccurrenceWith? signature
            source.plugLayout.plugRaw
            (ConcreteElaboration.compileRegion? signature
              source.plugLayout.plugRaw fuelSource)
            sourceContext sourceBinders
            (.child (source.plugLayout.frameRegion frameChild)) =
              some sourceItem := by
        simpa [PlugLayout.mapFrameOccurrence] using sourceCompiled
      have targetChildCompiled :
          ConcreteElaboration.compileOccurrenceWith? signature
            target.plugLayout.plugRaw
            (ConcreteElaboration.compileRegion? signature
              target.plugLayout.plugRaw fuelTarget)
            targetContext targetBinders
            (.child (presentation.regionMap
              (source.plugLayout.frameRegion frameChild))) =
                some targetItem := by
        simpa [PlugLayout.mapFrameOccurrence, castLocalOccurrence,
          presentation.regionMap_frameRegion] using targetCompiled
      have targetChildEq :
          target.plugLayout.frameRegion
              (Fin.cast presentation.frameRegionCountEq frameChild) =
            presentation.regionMap
              (source.plugLayout.frameRegion frameChild) :=
        (presentation.regionMap_frameRegion frameChild).symm
      have frameParent :
          (source.frame.val.regions frameChild).parent? = some source.site :=
        (ConcreteElaboration.mem_localOccurrences_child
          source.coalesceFrameRaw source.site frameChild).1 member
      cases frameKind : source.frame.val.regions frameChild with
      | sheet =>
          simp [frameKind, CRegion.parent?] at frameParent
      | cut actualParent =>
          have parentEq : actualParent = source.site := by
            rw [frameKind] at frameParent
            exact Option.some.inj frameParent
          subst actualParent
          have sourceKind :
              source.plugLayout.plugRaw.regions
                  (source.plugLayout.frameRegion frameChild) =
                .cut (source.plugLayout.frameRegion source.site) := by
            change source.plugLayout.plugRegion
                (source.plugLayout.frameRegion frameChild) =
              .cut (source.plugLayout.frameRegion source.site)
            rw [source.plugLayout.plugRegion_frameRegion]
            simp [frameKind, PlugLayout.mapFrameRegion]
          have targetKind :
              target.plugLayout.plugRaw.regions
                  (presentation.regionMap
                    (source.plugLayout.frameRegion frameChild)) =
                .cut (target.plugLayout.frameRegion target.site) := by
            have shape := presentation.region_shape_frameRegion frameChild
            rw [sourceKind] at shape
            simpa [mapRegionKind, presentation.regionMap_site] using shape
          have targetKindFrame :
              target.plugLayout.plugRaw.regions
                  (target.plugLayout.frameRegion
                    (Fin.cast presentation.frameRegionCountEq frameChild)) =
                .cut (target.plugLayout.frameRegion target.site) := by
            rw [targetChildEq]
            exact targetKind
          have sourcePlugParent :
              (source.plugLayout.plugRaw.regions
                (source.plugLayout.frameRegion frameChild)).parent? =
                  some (source.plugLayout.frameRegion source.site) := by
            rw [sourceKind]
            rfl
          have targetPlugParent :
              (target.plugLayout.plugRaw.regions
                (presentation.regionMap
                  (source.plugLayout.frameRegion frameChild))).parent? =
                  some (target.plugLayout.frameRegion target.site) := by
            rw [targetKind]
            rfl
          cases sourceResult :
              ConcreteElaboration.compileRegion? signature
                source.plugLayout.plugRaw fuelSource
                (source.plugLayout.frameRegion frameChild)
                sourceContext sourceBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?,
                sourceKind, sourceResult] at sourceChildCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?,
                sourceKind, sourceResult] at sourceChildCompiled
              subst sourceItem
              cases targetResult :
                  ConcreteElaboration.compileRegion? signature
                    target.plugLayout.plugRaw fuelTarget
                    (target.plugLayout.frameRegion
                      (Fin.cast presentation.frameRegionCountEq frameChild))
                    targetContext targetBinders with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    targetKindFrame, targetResult] at targetChildCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    targetKindFrame, targetResult] at targetChildCompiled
                  subst targetItem
                  have bodies := recurse
                    (child := source.plugLayout.frameRegion frameChild)
                    sourcePlugParent targetPlugParent
                    (presentation.allowed_cut siteDirection direction
                      (source.plugLayout.frameRegion frameChild)
                      (source.plugLayout.frameRegion source.site)
                      sourceKind allowed)
                    bindersRelated
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.cutChild
                      (source.plugLayout.plugRaw_wellFormed signature source
                        sourceAdmissible) sourceKind)
                    (targetEnumeration.cutChild
                      (target.plugLayout.plugRaw_wellFormed signature target
                        targetAdmissible) targetKind)
                    sourceResult (by
                      simpa [presentation.regionMap_frameRegion] using
                        targetResult)
                  intro sourceEnv targetEnv relEnv environments
                  have bodyEntailment :=
                    bodies sourceEnv targetEnv relEnv environments
                  simp only [cut_denotes_negation]
                  cases direction with
                  | forward =>
                      exact fun sourceNot targetDenotes =>
                        sourceNot (bodyEntailment targetDenotes)
                  | backward =>
                      exact fun targetNot sourceDenotes =>
                        targetNot (bodyEntailment sourceDenotes)
      | bubble actualParent arity =>
          have parentEq : actualParent = source.site := by
            rw [frameKind] at frameParent
            exact Option.some.inj frameParent
          subst actualParent
          have sourceKind :
              source.plugLayout.plugRaw.regions
                  (source.plugLayout.frameRegion frameChild) =
                .bubble (source.plugLayout.frameRegion source.site) arity := by
            change source.plugLayout.plugRegion
                (source.plugLayout.frameRegion frameChild) =
              .bubble (source.plugLayout.frameRegion source.site) arity
            rw [source.plugLayout.plugRegion_frameRegion]
            simp [frameKind, PlugLayout.mapFrameRegion]
          have targetKind :
              target.plugLayout.plugRaw.regions
                  (presentation.regionMap
                    (source.plugLayout.frameRegion frameChild)) =
                .bubble (target.plugLayout.frameRegion target.site) arity := by
            have shape := presentation.region_shape_frameRegion frameChild
            rw [sourceKind] at shape
            simpa [mapRegionKind, presentation.regionMap_site] using shape
          have targetKindFrame :
              target.plugLayout.plugRaw.regions
                  (target.plugLayout.frameRegion
                    (Fin.cast presentation.frameRegionCountEq frameChild)) =
                .bubble (target.plugLayout.frameRegion target.site) arity := by
            rw [targetChildEq]
            exact targetKind
          have sourcePlugParent :
              (source.plugLayout.plugRaw.regions
                (source.plugLayout.frameRegion frameChild)).parent? =
                  some (source.plugLayout.frameRegion source.site) := by
            rw [sourceKind]
            rfl
          have targetPlugParent :
              (target.plugLayout.plugRaw.regions
                (presentation.regionMap
                  (source.plugLayout.frameRegion frameChild))).parent? =
                  some (target.plugLayout.frameRegion target.site) := by
            rw [targetKind]
            rfl
          let sourcePushed :=
            sourceBinders.push
              (source.plugLayout.frameRegion frameChild) arity
          let targetPushed :=
            targetBinders.push
              (target.plugLayout.frameRegion
                (Fin.cast presentation.frameRegionCountEq frameChild)) arity
          cases sourceResult :
              ConcreteElaboration.compileRegion? signature
                source.plugLayout.plugRaw fuelSource
                (source.plugLayout.frameRegion frameChild)
                sourceContext sourcePushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?,
                sourceKind, sourcePushed, sourceResult] at sourceChildCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?,
                sourceKind, sourcePushed, sourceResult] at sourceChildCompiled
              subst sourceItem
              cases targetResult :
                  ConcreteElaboration.compileRegion? signature
                    target.plugLayout.plugRaw fuelTarget
                    (target.plugLayout.frameRegion
                      (Fin.cast presentation.frameRegionCountEq frameChild))
                    targetContext targetPushed with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    targetKindFrame, targetPushed, targetResult]
                    at targetChildCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?,
                    targetKindFrame, targetPushed, targetResult]
                    at targetChildCompiled
                  subst targetItem
                  have pushedRelated :=
                    presentation.binders_push_frameRegion bindersRelated
                      frameChild arity
                  have pushedRelatedMapped :
                      presentation.BinderRelated
                        (sourceBinders.push
                          (source.plugLayout.frameRegion frameChild) arity)
                        (targetBinders.push
                          (presentation.regionMap
                            (source.plugLayout.frameRegion frameChild)) arity) := by
                    simpa [presentation.regionMap_frameRegion] using
                      pushedRelated
                  have bodies := recurse
                    (child := source.plugLayout.frameRegion frameChild)
                    (childTargetBinders := targetBinders.push
                      (presentation.regionMap
                        (source.plugLayout.frameRegion frameChild)) arity)
                    sourcePlugParent targetPlugParent
                    (presentation.allowed_bubble siteDirection direction
                      (source.plugLayout.frameRegion frameChild)
                      (source.plugLayout.frameRegion source.site) arity
                      sourceKind allowed)
                    pushedRelatedMapped
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.bubbleChild
                      (source.plugLayout.plugRaw_wellFormed signature source
                        sourceAdmissible) sourceKind)
                    (targetEnumeration.bubbleChild
                      (target.plugLayout.plugRaw_wellFormed signature target
                        targetAdmissible) targetKind)
                    sourceResult (by
                      simpa [presentation.regionMap_frameRegion, targetPushed]
                        using targetResult)
                  intro sourceEnv targetEnv relEnv environments
                  simp only [bubble_denotes_exists]
                  cases direction with
                  | forward =>
                      rintro ⟨relationValue, sourceDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv
                          (relationValue, relEnv) environments sourceDenotes⟩
                  | backward =>
                      rintro ⟨relationValue, targetDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv
                          (relationValue, relEnv) environments targetDenotes⟩

end TwoInputPresentation

end VisualProof.Diagram.Splice.Input
