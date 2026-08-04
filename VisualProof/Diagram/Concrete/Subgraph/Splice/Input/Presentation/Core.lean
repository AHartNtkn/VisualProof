import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Semantics.FocusedEnvironment

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace TwoInputPresentation

private theorem paired_allFin_succ_last (n : Nat) :
    VisualProof.Data.Finite.allFin (n + 1) =
      (VisualProof.Data.Finite.allFin n).map (Fin.castAdd 1) ++
        [Fin.last n] := by
  rw [VisualProof.Data.Finite.allFin_eq_finRange,
    VisualProof.Data.Finite.allFin_eq_finRange, List.finRange_succ_last]
  apply congrArg (fun xs : List (Fin (n + 1)) => xs ++ [Fin.last n])
  apply List.map_congr_left
  intro index _
  apply Fin.ext
  rfl

private theorem paired_allFin_add (n m : Nat) :
    VisualProof.Data.Finite.allFin (n + m) =
      (VisualProof.Data.Finite.allFin n).map (Fin.castAdd m) ++
        (VisualProof.Data.Finite.allFin m).map (Fin.natAdd n) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, VisualProof.Data.Finite.allFin, List.map_nil,
        List.append_nil]
      have hfun : (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id := by
        funext index
        apply Fin.ext
        rfl
      rw [hfun, List.map_id]
  | succ m ih =>
      change VisualProof.Data.Finite.allFin ((n + m) + 1) = _
      rw [paired_allFin_succ_last (n + m), ih, List.map_append,
        paired_allFin_succ_last m, List.map_append, List.map_map,
        List.append_assoc]
      simp only [List.map_map]
      have hleft :
          (Fin.castAdd 1 ∘ Fin.castAdd m : Fin n → Fin ((n + m) + 1)) =
            Fin.castAdd (m + 1) := by
        funext index
        apply Fin.ext
        rfl
      have hmiddle :
          (Fin.castAdd 1 ∘ Fin.natAdd n : Fin m → Fin ((n + m) + 1)) =
            (Fin.natAdd n ∘ Fin.castAdd 1) := by
        funext index
        apply Fin.ext
        rfl
      have hlast : Fin.last (n + m) = Fin.natAdd n (Fin.last m) := by
        apply Fin.ext
        rfl
      rw [hleft, hmiddle, hlast]
      rfl

theorem paired_allFin_layout_nodes (layout : PlugLayout input) :
    VisualProof.Data.Finite.allFin layout.plugRaw.nodeCount =
      (VisualProof.Data.Finite.allFin input.frame.val.nodeCount).map
          layout.frameNode ++
        (VisualProof.Data.Finite.allFin
          input.pattern.val.diagram.nodeCount).map layout.patternNode := by
  simpa [PlugLayout.plugRaw, PlugLayout.nodeCount, PlugLayout.frameNode,
    PlugLayout.patternNode] using paired_allFin_add input.frame.val.nodeCount
      input.pattern.val.diagram.nodeCount

theorem paired_allFin_layout_regions (layout : PlugLayout input) :
    VisualProof.Data.Finite.allFin layout.plugRaw.regionCount =
      (VisualProof.Data.Finite.allFin input.frame.val.regionCount).map
          layout.frameRegion ++
        (VisualProof.Data.Finite.allFin layout.materialRegions.count).map
          layout.materialRegion := by
  simpa [PlugLayout.plugRaw, PlugLayout.regionCount, PlugLayout.frameRegion,
    PlugLayout.materialRegion] using paired_allFin_add
      input.frame.val.regionCount layout.materialRegions.count

private theorem paired_allFin_map_survivor_origin
    (domain : SurvivorDomain size) :
    (VisualProof.Data.Finite.allFin domain.count).map domain.origin =
      domain.enumeration := by
  rw [VisualProof.Data.Finite.allFin_eq_finRange, List.finRange,
    List.map_ofFn]
  change List.ofFn (fun index => domain.enumeration.get index) =
    domain.enumeration
  exact List.ofFn_getElem

private theorem filter_frameNodes_eq_nil_at_material
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    List.filter
        (fun node => decide
          ((layout.plugNode node).region = layout.bodyRegion region))
        ((VisualProof.Data.Finite.allFin input.frame.val.nodeCount).map
          layout.frameNode) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro node member
  rw [List.mem_filter, List.mem_map] at member
  rcases member with ⟨⟨frameNode, _, rfl⟩, selected⟩
  have equality := decide_eq_true_iff.mp selected
  rw [layout.plugNode_frameNode, layout.mapFrameNode_region,
    layout.bodyRegion_material region hregion] at equality
  exact layout.frameRegion_ne_materialRegion _ _ equality

private theorem filter_patternNodes_at_material
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    List.filter
        (fun node => decide
          ((layout.plugNode node).region = layout.bodyRegion region))
        ((VisualProof.Data.Finite.allFin
          input.pattern.val.diagram.nodeCount).map layout.patternNode) =
      ((VisualProof.Data.Finite.allFin
        input.pattern.val.diagram.nodeCount).filter
          fun node => decide
            ((input.pattern.val.diagram.nodes node).region = region)).map
              layout.patternNode := by
  rw [List.filter_map]
  apply congrArg (List.map layout.patternNode)
  apply List.filter_congr
  intro node _
  change decide
      ((layout.plugNode (layout.patternNode node)).region =
        layout.bodyRegion region) =
    decide ((input.pattern.val.diagram.nodes node).region = region)
  apply decide_eq_decide.mpr
  constructor
  · intro equality
    rw [layout.plugNode_patternNode, layout.mapPatternNode_region] at equality
    by_cases hnode : input.binderSpine.IsMaterialRegion
        (input.pattern.val.diagram.nodes node).region
    · exact layout.bodyRegion_injective_of_material hnode hregion equality
    · rw [layout.bodyRegion_nonmaterial _ hnode,
        layout.bodyRegion_material region hregion] at equality
      exact False.elim (layout.frameRegion_ne_materialRegion _ _ equality)
  · intro equality
    subst region
    rw [layout.plugNode_patternNode, layout.mapPatternNode_region]

private theorem filter_frameChildren_eq_nil_at_material
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    List.filter
        (fun child => decide
          ((layout.plugRegion child).parent? = some (layout.bodyRegion region)))
        ((VisualProof.Data.Finite.allFin input.frame.val.regionCount).map
          layout.frameRegion) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro child member
  rw [List.mem_filter, List.mem_map] at member
  rcases member with ⟨⟨frameChild, _, rfl⟩, selected⟩
  have equality := decide_eq_true_iff.mp selected
  rw [layout.plugRegion_frameRegion] at equality
  cases kind : input.frame.val.regions frameChild with
  | sheet => simp [kind, PlugLayout.mapFrameRegion, CRegion.parent?] at equality
  | cut parent =>
      have mapped : layout.frameRegion parent = layout.bodyRegion region :=
        Option.some.inj (by
          simpa [kind, PlugLayout.mapFrameRegion, CRegion.parent?] using equality)
      rw [layout.bodyRegion_material region hregion] at mapped
      exact layout.frameRegion_ne_materialRegion _ _ mapped
  | bubble parent arity =>
      have mapped : layout.frameRegion parent = layout.bodyRegion region :=
        Option.some.inj (by
          simpa [kind, PlugLayout.mapFrameRegion, CRegion.parent?] using equality)
      rw [layout.bodyRegion_material region hregion] at mapped
      exact layout.frameRegion_ne_materialRegion _ _ mapped

private theorem filter_materialChildren_at_material
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    List.filter
        (fun child => decide
          ((layout.plugRegion child).parent? = some (layout.bodyRegion region)))
        ((VisualProof.Data.Finite.allFin layout.materialRegions.count).map
          layout.materialRegion) =
      ((VisualProof.Data.Finite.allFin
        input.pattern.val.diagram.regionCount).filter
          fun child => decide
            ((input.pattern.val.diagram.regions child).parent? = some region)).map
              layout.bodyRegion := by
  let parentPredicate := fun child : Fin input.pattern.val.diagram.regionCount =>
    decide ((input.pattern.val.diagram.regions child).parent? = some region)
  have selectedSurvives : ∀ child,
      parentPredicate child = true →
        layout.materialRegions.survives child = true := by
    intro child selected
    have parent := decide_eq_true_iff.mp selected
    have material := PlugLayout.directChildOfMaterial_material input region child
      hregion parent
    exact (layout.materialRegions_survives_iff child).2 material
  rw [List.filter_map]
  have predicateEq : ∀ material : layout.materialRegions.Carrier,
      decide
          ((layout.plugRegion (layout.materialRegion material)).parent? =
            some (layout.bodyRegion region)) =
        parentPredicate (layout.materialRegions.origin material) := by
    intro material
    change decide
        ((layout.plugRegion (layout.materialRegion material)).parent? =
          some (layout.bodyRegion region)) =
      decide
        ((input.pattern.val.diagram.regions
          (layout.materialRegions.origin material)).parent? = some region)
    apply decide_eq_decide.mpr
    rw [layout.plugRegion_materialRegion]
    have hmaterial : input.binderSpine.IsMaterialRegion
        (layout.materialRegions.origin material) :=
      (layout.materialRegions_survives_iff _).1
        (layout.materialRegions.origin_survives material)
    cases kind : input.pattern.val.diagram.regions
        (layout.materialRegions.origin material) with
    | sheet =>
        simp only [PlugLayout.mapPatternRegion, CRegion.parent?]
        constructor
        · intro equality
          have bodyEq := Option.some.inj equality
          rw [layout.bodyRegion_material region hregion] at bodyEq
          exact False.elim
            (layout.frameRegion_ne_materialRegion _ _ bodyEq)
        · intro equality
          contradiction
    | cut parent =>
        simp only [kind, PlugLayout.mapPatternRegion, CRegion.parent?]
        constructor <;> intro equality
        · have bodyEq := Option.some.inj equality
          by_cases hparent : input.binderSpine.IsMaterialRegion parent
          · exact congrArg some
              (layout.bodyRegion_injective_of_material hparent hregion bodyEq)
          · rw [layout.bodyRegion_nonmaterial parent hparent,
                layout.bodyRegion_material region hregion] at bodyEq
            exact False.elim
              (layout.frameRegion_ne_materialRegion _ _ bodyEq)
        · exact congrArg (fun parent => some (layout.bodyRegion parent))
            (Option.some.inj equality)
    | bubble parent arity =>
        simp only [kind, PlugLayout.mapPatternRegion, CRegion.parent?]
        constructor <;> intro equality
        · have bodyEq := Option.some.inj equality
          by_cases hparent : input.binderSpine.IsMaterialRegion parent
          · exact congrArg some
              (layout.bodyRegion_injective_of_material hparent hregion bodyEq)
          · rw [layout.bodyRegion_nonmaterial parent hparent,
                layout.bodyRegion_material region hregion] at bodyEq
            exact False.elim
              (layout.frameRegion_ne_materialRegion _ _ bodyEq)
        · exact congrArg (fun parent => some (layout.bodyRegion parent))
            (Option.some.inj equality)
  have filteredEq :
      List.filter
          ((fun child => decide
            ((layout.plugRegion child).parent? =
              some (layout.bodyRegion region))) ∘ layout.materialRegion)
          (VisualProof.Data.Finite.allFin layout.materialRegions.count) =
        List.filter (parentPredicate ∘ layout.materialRegions.origin)
          (VisualProof.Data.Finite.allFin layout.materialRegions.count) := by
    apply List.filter_congr
    intro material _
    exact predicateEq material
  rw [filteredEq]
  calc
    _ = (List.filter (parentPredicate ∘ layout.materialRegions.origin)
          (VisualProof.Data.Finite.allFin layout.materialRegions.count)).map
            (layout.bodyRegion ∘ layout.materialRegions.origin) := by
      apply List.map_congr_left
      intro material _
      exact (layout.bodyRegion_origin material).symm
    _ = (List.filter parentPredicate
          ((VisualProof.Data.Finite.allFin layout.materialRegions.count).map
            layout.materialRegions.origin)).map layout.bodyRegion := by
      rw [List.filter_map, List.map_map]
    _ = (List.filter parentPredicate layout.materialRegions.enumeration).map
          layout.bodyRegion := by
      rw [paired_allFin_map_survivor_origin]
    _ = (List.filter parentPredicate
          (VisualProof.Data.Finite.allFin
            input.pattern.val.diagram.regionCount)).map
          layout.bodyRegion := by
      unfold SurvivorDomain.enumeration VisualProof.Data.Finite.filterFin
      rw [List.filter_filter]
      have filtersEq :
          List.filter
              (fun child => parentPredicate child &&
                layout.materialRegions.survives child)
              (VisualProof.Data.Finite.allFin
                input.pattern.val.diagram.regionCount) =
            List.filter parentPredicate
              (VisualProof.Data.Finite.allFin
                input.pattern.val.diagram.regionCount) := by
        apply List.filter_congr
        intro child _
        cases selected : parentPredicate child with
        | false => rfl
        | true =>
            rw [selectedSurvives child selected]
            rfl
      rw [filtersEq]
    _ = _ := rfl

theorem PlugLayout.localOccurrences_bodyRegion
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.bodyRegion region) =
      (ConcreteElaboration.localOccurrences input.pattern.val.diagram
        region).map layout.mapPatternOccurrence := by
  unfold ConcreteElaboration.localOccurrences
    VisualProof.Data.Finite.filterFin
  change
    ((VisualProof.Data.Finite.allFin layout.plugRaw.nodeCount).filter
        fun node => decide
          ((layout.plugNode node).region = layout.bodyRegion region)).map
          ConcreteElaboration.LocalOccurrence.node ++
      ((VisualProof.Data.Finite.allFin layout.plugRaw.regionCount).filter
        fun child => decide
          ((layout.plugRegion child).parent? =
            some (layout.bodyRegion region))).map
              ConcreteElaboration.LocalOccurrence.child =
    ((((VisualProof.Data.Finite.allFin
      input.pattern.val.diagram.nodeCount).filter
        fun node => decide
          ((input.pattern.val.diagram.nodes node).region = region)).map
            ConcreteElaboration.LocalOccurrence.node ++
      ((VisualProof.Data.Finite.allFin
        input.pattern.val.diagram.regionCount).filter
        fun child => decide
          ((input.pattern.val.diagram.regions child).parent? = some region)).map
            ConcreteElaboration.LocalOccurrence.child).map
              layout.mapPatternOccurrence)
  rw [paired_allFin_layout_nodes, paired_allFin_layout_regions]
  simp only [List.filter_append, List.map_append, List.map_map,
    filter_frameNodes_eq_nil_at_material layout region hregion,
    filter_patternNodes_at_material layout region hregion,
    filter_frameChildren_eq_nil_at_material layout region hregion,
    filter_materialChildren_at_material layout region hregion,
    List.map_nil, List.nil_append]
  rfl

theorem checkedDiagram_regions_eq
    (left right : CheckedDiagram signature) (h : left = right)
    (region : Fin left.val.regionCount) :
    left.val.regions region =
      cast (congrArg CRegion
        (congrArg (fun checked : CheckedDiagram signature =>
          checked.val.regionCount) h).symm)
        (right.val.regions (Fin.cast
          (congrArg (fun checked : CheckedDiagram signature =>
            checked.val.regionCount) h) region)) := by
  subst right
  rfl

theorem checkedDiagram_regions_rename_eq
    (left right : CheckedDiagram signature) (h : left = right)
    (region : Fin left.val.regionCount) :
    right.val.regions (Fin.cast (congrArg
      (fun checked : CheckedDiagram signature => checked.val.regionCount) h)
      region) =
      (left.val.regions region).rename
        (FiniteEquiv.finCast (congrArg
          (fun checked : CheckedDiagram signature => checked.val.regionCount) h)) := by
  cases h
  cases hregion : left.val.regions region <;>
    simp [hregion, FiniteEquiv.finCast, CRegion.rename]

theorem checkedDiagram_nodes_eq
    (left right : CheckedDiagram signature) (h : left = right)
    (node : Fin left.val.nodeCount) :
    left.val.nodes node =
      cast (congrArg CNode
        (congrArg (fun checked : CheckedDiagram signature =>
          checked.val.regionCount) h).symm)
        (right.val.nodes (Fin.cast
          (congrArg (fun checked : CheckedDiagram signature =>
            checked.val.nodeCount) h) node)) := by
  subst right
  rfl

theorem checkedDiagram_nodes_rename_eq
    (left right : CheckedDiagram signature) (h : left = right)
    (node : Fin left.val.nodeCount) :
    right.val.nodes (Fin.cast (congrArg
      (fun checked : CheckedDiagram signature => checked.val.nodeCount) h)
      node) =
      (left.val.nodes node).rename
        (FiniteEquiv.finCast (congrArg
          (fun checked : CheckedDiagram signature =>
            checked.val.regionCount) h)) := by
  cases h
  cases hnode : left.val.nodes node <;>
    simp [hnode, FiniteEquiv.finCast, CNode.rename]

theorem checkedDiagram_endpointOccurs_eq
    (left right : CheckedDiagram signature) (h : left = right)
    (wire : Fin left.val.wireCount)
    (endpoint : CEndpoint left.val.nodeCount) :
    left.val.EndpointOccurs wire endpoint ↔
      right.val.EndpointOccurs
        (Fin.cast (congrArg
          (fun checked : CheckedDiagram signature => checked.val.wireCount) h)
          wire)
        { node := Fin.cast (congrArg
            (fun checked : CheckedDiagram signature => checked.val.nodeCount) h)
            endpoint.node
          port := endpoint.port } := by
  cases h
  rfl

def castLocalOccurrence
    (left right : CheckedDiagram signature)
    (regionEq : left.val.regionCount = right.val.regionCount)
    (nodeEq : left.val.nodeCount = right.val.nodeCount) :
    ConcreteElaboration.LocalOccurrence left.val.regionCount left.val.nodeCount →
      ConcreteElaboration.LocalOccurrence right.val.regionCount
        right.val.nodeCount
  | .node node => .node (Fin.cast nodeEq node)
  | .child region => .child (Fin.cast regionEq region)

theorem checkedDiagram_localOccurrences_eq
    (left right : CheckedDiagram signature) (h : left = right)
    (region : Fin left.val.regionCount) :
    ConcreteElaboration.localOccurrences right.val
        (Fin.cast (congrArg
          (fun checked : CheckedDiagram signature => checked.val.regionCount) h)
          region) =
      (ConcreteElaboration.localOccurrences left.val region).map
        (castLocalOccurrence
          left right
          (congrArg
            (fun checked : CheckedDiagram signature => checked.val.regionCount) h)
          (congrArg
            (fun checked : CheckedDiagram signature => checked.val.nodeCount) h)) := by
  cases h
  have regionCast :
      (Fin.cast (congrArg
        (fun checked : CheckedDiagram signature => checked.val.regionCount)
          (Eq.refl left)) : Fin left.val.regionCount → Fin left.val.regionCount) =
        id := by
    funext index
    apply Fin.ext
    rfl
  have nodeCast :
      (Fin.cast (congrArg
        (fun checked : CheckedDiagram signature => checked.val.nodeCount)
          (Eq.refl left)) : Fin left.val.nodeCount → Fin left.val.nodeCount) =
        id := by
    funext index
    apply Fin.ext
    rfl
  rw [regionCast]
  have occurrenceCast :
      castLocalOccurrence left left
          (congrArg
            (fun checked : CheckedDiagram signature => checked.val.regionCount)
            (Eq.refl left))
          (congrArg
            (fun checked : CheckedDiagram signature => checked.val.nodeCount)
            (Eq.refl left)) = id := by
    funext occurrence
    cases occurrence <;>
      simp [castLocalOccurrence, regionCast, nodeCast]
  rw [occurrenceCast, List.map_id]
  simp

def frameRegionCountEq (presentation : TwoInputPresentation source target) :
    source.frame.val.regionCount = target.frame.val.regionCount :=
  congrArg (fun checked => checked.val.regionCount) presentation.frame_eq

def frameWireCountEq (presentation : TwoInputPresentation source target) :
    source.frame.val.wireCount = target.frame.val.wireCount :=
  congrArg (fun checked => checked.val.wireCount) presentation.frame_eq

def frameNodeCountEq (presentation : TwoInputPresentation source target) :
    source.frame.val.nodeCount = target.frame.val.nodeCount :=
  congrArg (fun checked => checked.val.nodeCount) presentation.frame_eq

theorem checkedDiagram_root_eq
    (left right : CheckedDiagram signature) (h : left = right) :
    Fin.cast (congrArg (fun checked : CheckedDiagram signature =>
      checked.val.regionCount) h) left.val.root = right.val.root := by
  subst right
  rfl

theorem checkedDiagram_wire_scope_eq
    (left right : CheckedDiagram signature) (h : left = right)
    (wire : Fin left.val.wireCount) :
    Fin.cast (congrArg (fun checked : CheckedDiagram signature =>
      checked.val.regionCount) h) (left.val.wires wire).scope =
      (right.val.wires (Fin.cast (congrArg
        (fun checked : CheckedDiagram signature => checked.val.wireCount) h)
        wire)).scope := by
  subst right
  rfl

private theorem checkedDiagram_encloses_eq
    (left right : CheckedDiagram signature) (h : left = right)
    (ancestor descendant : Fin left.val.regionCount) :
    left.val.Encloses ancestor descendant ↔
      right.val.Encloses
        (Fin.cast (congrArg (fun checked : CheckedDiagram signature =>
          checked.val.regionCount) h) ancestor)
        (Fin.cast (congrArg (fun checked : CheckedDiagram signature =>
          checked.val.regionCount) h) descendant) := by
  subst right
  rfl

/-- Transport a caller's ordered retained-frame boundary to the paired target
frame. `List.map` preserves positions and repetitions exactly. -/
def targetBoundary (presentation : TwoInputPresentation source target)
    (boundary : List (Fin source.frame.val.wireCount)) :
    List (Fin target.frame.val.wireCount) :=
  boundary.map (Fin.cast presentation.frameWireCountEq)

@[simp] theorem targetBoundary_length
    (presentation : TwoInputPresentation source target)
    (boundary : List (Fin source.frame.val.wireCount)) :
    (presentation.targetBoundary boundary).length = boundary.length := by
  simp [targetBoundary]

theorem targetBoundary_root
    (presentation : TwoInputPresentation source target)
    (boundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (source.frame.val.wires wire).scope = source.frame.val.root) :
    ∀ wire, wire ∈ presentation.targetBoundary boundary →
      (target.frame.val.wires wire).scope = target.frame.val.root := by
  intro wire hwire
  rw [targetBoundary, List.mem_map] at hwire
  obtain ⟨original, horiginal, rfl⟩ := hwire
  have scopeEq : Fin.cast presentation.frameRegionCountEq
        (source.frame.val.wires original).scope =
      (target.frame.val.wires
        (Fin.cast presentation.frameWireCountEq original)).scope := by
    exact checkedDiagram_wire_scope_eq source.frame target.frame
      presentation.frame_eq original
  have rootEq : Fin.cast presentation.frameRegionCountEq
      source.frame.val.root = target.frame.val.root := by
    exact checkedDiagram_root_eq source.frame target.frame presentation.frame_eq
  rw [← scopeEq, sourceRoot original horiginal, rootEq]

/-- Corresponding quotient copies of one retained-frame wire are visible at
the paired splice sites exactly together. -/
theorem coalescedFrame_wire_visible_at_site_iff
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (wire : Fin source.frame.val.wireCount) :
    source.coalesceFrameRaw.Encloses
        (source.coalesceFrameRaw.wires
          (source.quotientWire wire)).scope source.site ↔
      target.coalesceFrameRaw.Encloses
        (target.coalesceFrameRaw.wires
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire))).scope
        target.site := by
  rw [source.quotientWire_visible_at_site_iff sourceAdmissible,
    target.quotientWire_visible_at_site_iff targetAdmissible]
  have visible := checkedDiagram_encloses_eq source.frame target.frame
    presentation.frame_eq (source.frame.val.wires wire).scope source.site
  rw [checkedDiagram_wire_scope_eq source.frame target.frame
    presentation.frame_eq wire, presentation.site_eq] at visible
  exact visible

/-- A quotient class containing a wire bound outside the splice site has the
same outermost scope in both presentations. The site-local quotient condition
makes the two class-member sets identical; admissibility makes each coalesced
scope their common outermost member. -/
theorem coalescedScope_eq_of_nonSite_wire
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (wire : Fin source.frame.val.wireCount)
    (nonSite : (source.frame.val.wires wire).scope ≠ source.site) :
    Fin.cast presentation.frameRegionCountEq
        (source.coalescedScope (source.quotientWire wire)) =
      target.coalescedScope
        (target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire)) := by
  let sourceClass := source.quotientWire wire
  let targetWire := Fin.cast presentation.frameWireCountEq wire
  let targetClass := target.quotientWire targetWire
  obtain ⟨sourceMember, sourceMemberIn, sourceScope⟩ :=
    source.coalescedScope_eq_member_scope sourceClass
  obtain ⟨targetMember, targetMemberIn, targetScope⟩ :=
    target.coalescedScope_eq_member_scope targetClass
  let targetMemberSource :=
    Fin.cast presentation.frameWireCountEq.symm targetMember
  have targetMemberCast :
      Fin.cast presentation.frameWireCountEq targetMemberSource =
        targetMember := by
    apply Fin.ext
    rfl
  have sourceMemberClass :
      source.quotientWire sourceMember = source.quotientWire wire := by
    exact (source.mem_classWires sourceClass sourceMember).1
      sourceMemberIn
  have targetSourceMemberClass :
      target.quotientWire
          (Fin.cast presentation.frameWireCountEq sourceMember) =
        target.quotientWire targetWire := by
    exact (presentation.site_local_quotients sourceMember wire
      (Or.inr nonSite)).1 sourceMemberClass
  have targetSourceMemberIn :
      Fin.cast presentation.frameWireCountEq sourceMember ∈
        target.classWires targetClass := by
    exact (target.mem_classWires targetClass _).2 targetSourceMemberClass
  have targetMemberClass :
      target.quotientWire targetMember =
        target.quotientWire targetWire := by
    exact (target.mem_classWires targetClass targetMember).1 targetMemberIn
  have sourceTargetMemberClass :
      source.quotientWire targetMemberSource =
        source.quotientWire wire := by
    apply (presentation.site_local_quotients targetMemberSource wire
      (Or.inr nonSite)).2
    simpa only [targetMemberCast] using targetMemberClass
  have sourceTargetMemberIn :
      targetMemberSource ∈ source.classWires sourceClass := by
    exact (source.mem_classWires sourceClass targetMemberSource).2
      sourceTargetMemberClass
  have targetEnclosesSource :
      target.frame.val.Encloses
        (target.coalescedScope targetClass)
        (Fin.cast presentation.frameRegionCountEq
          (source.coalescedScope sourceClass)) := by
    have encloses := target.coalescedScope_encloses_member targetAdmissible
      targetClass (Fin.cast presentation.frameWireCountEq sourceMember)
      targetSourceMemberIn
    rw [sourceScope,
      checkedDiagram_wire_scope_eq source.frame target.frame
        presentation.frame_eq sourceMember]
    exact encloses
  have sourceEnclosesTarget :
      target.frame.val.Encloses
        (Fin.cast presentation.frameRegionCountEq
          (source.coalescedScope sourceClass))
        (target.coalescedScope targetClass) := by
    have encloses := source.coalescedScope_encloses_member sourceAdmissible
      sourceClass targetMemberSource sourceTargetMemberIn
    have transported :=
      (checkedDiagram_encloses_eq source.frame target.frame
        presentation.frame_eq
        (source.coalescedScope sourceClass)
        (source.frame.val.wires targetMemberSource).scope).1 encloses
    rw [checkedDiagram_wire_scope_eq source.frame target.frame
        presentation.frame_eq targetMemberSource,
      targetMemberCast, ← targetScope] at transported
    exact transported
  exact ConcreteElaboration.checked_encloses_antisymm target.frame.property
    sourceEnclosesTarget targetEnclosesSource

/-- Canonical target quotient represented by a source quotient. Away from the
site, locality makes this independent of the chosen source representative. -/
def quotientMap
    (presentation : TwoInputPresentation source target)
    (quotient : source.wireQuotient.Carrier) :
    target.wireQuotient.Carrier :=
  target.quotientWire
    (Fin.cast presentation.frameWireCountEq
      (source.wireQuotient.origin quotient))

theorem quotientMap_quotientWire_of_nonSite
    (presentation : TwoInputPresentation source target)
    (wire : Fin source.frame.val.wireCount)
    (nonSite : (source.frame.val.wires wire).scope ≠ source.site) :
    presentation.quotientMap (source.quotientWire wire) =
      target.quotientWire
        (Fin.cast presentation.frameWireCountEq wire) := by
  unfold quotientMap
  apply (presentation.site_local_quotients
    (source.wireQuotient.origin (source.quotientWire wire)) wire
    (Or.inr nonSite)).1
  exact source.quotientWire_wireQuotient_origin
    (source.quotientWire wire)

/-- Exact non-site scope is preserved by the canonical quotient map. -/
theorem quotientMap_coalescedScope
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site)
    (quotient : source.wireQuotient.Carrier)
    (scope : source.coalescedScope quotient = region) :
    target.coalescedScope (presentation.quotientMap quotient) =
      Fin.cast presentation.frameRegionCountEq region := by
  obtain ⟨wire, member, wireScope⟩ :=
    source.coalescedScope_eq_member_scope quotient
  have quotientEq : source.quotientWire wire = quotient :=
    (source.mem_classWires quotient wire).1 member
  have wireNonSite : (source.frame.val.wires wire).scope ≠ source.site := by
    rw [← wireScope, scope]
    exact regionNe
  have mappedEq :
      presentation.quotientMap quotient =
        target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire) := by
    rw [← quotientEq]
    exact presentation.quotientMap_quotientWire_of_nonSite wire wireNonSite
  have coalesced := presentation.coalescedScope_eq_of_nonSite_wire
    sourceAdmissible targetAdmissible wire wireNonSite
  rw [quotientEq, scope, ← mappedEq] at coalesced
  exact coalesced.symm

/-- A shared original wire whose source quotient is bound at a regular scope
is represented by the canonical quotient map, even when that particular
original wire is itself bound at the splice site. -/
theorem quotientMap_quotientWire_of_coalescedScope
    (presentation : TwoInputPresentation source target)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site)
    (wire : Fin source.frame.val.wireCount)
    (scope :
      source.coalescedScope (source.quotientWire wire) = region) :
    presentation.quotientMap (source.quotientWire wire) =
      target.quotientWire
        (Fin.cast presentation.frameWireCountEq wire) := by
  obtain ⟨representative, member, representativeScope⟩ :=
    source.coalescedScope_eq_member_scope (source.quotientWire wire)
  have representativeClass :
      source.quotientWire representative = source.quotientWire wire :=
    (source.mem_classWires (source.quotientWire wire) representative).1 member
  have representativeNonSite :
      (source.frame.val.wires representative).scope ≠ source.site := by
    rw [← representativeScope, scope]
    exact regionNe
  have targetClass :
      target.quotientWire
          (Fin.cast presentation.frameWireCountEq representative) =
        target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire) :=
    (presentation.site_local_quotients representative wire
      (Or.inl representativeNonSite)).1 representativeClass
  rw [← representativeClass,
    presentation.quotientMap_quotientWire_of_nonSite representative
      representativeNonSite]
  exact targetClass

/-- Corresponding quotient copies of any shared original wire have paired
coalesced scopes at every regular frame region. -/
theorem related_coalescedScope_iff
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site)
    (wire : Fin source.frame.val.wireCount) :
    source.coalescedScope (source.quotientWire wire) = region ↔
      target.coalescedScope
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) =
        Fin.cast presentation.frameRegionCountEq region := by
  constructor
  · intro sourceScope
    have mappedScope := presentation.quotientMap_coalescedScope
      sourceAdmissible targetAdmissible region regionNe
      (source.quotientWire wire) sourceScope
    rw [presentation.quotientMap_quotientWire_of_coalescedScope region
      regionNe wire sourceScope] at mappedScope
    exact mappedScope
  · intro targetScope
    let targetWire := Fin.cast presentation.frameWireCountEq wire
    obtain ⟨targetRepresentative, targetMember, targetRepresentativeScope⟩ :=
      target.coalescedScope_eq_member_scope
        (target.quotientWire targetWire)
    let sourceRepresentative :=
      Fin.cast presentation.frameWireCountEq.symm targetRepresentative
    have targetRepresentativeCast :
        Fin.cast presentation.frameWireCountEq sourceRepresentative =
          targetRepresentative := by
      apply Fin.ext
      rfl
    have sourceRepresentativeScope :
        (source.frame.val.wires sourceRepresentative).scope = region := by
      have transported := checkedDiagram_wire_scope_eq source.frame target.frame
        presentation.frame_eq sourceRepresentative
      rw [targetRepresentativeCast, ← targetRepresentativeScope,
        targetScope] at transported
      have values :
          (Fin.cast presentation.frameRegionCountEq
            (source.frame.val.wires sourceRepresentative).scope).val =
          (Fin.cast presentation.frameRegionCountEq region).val :=
        congrArg (fun index => index.val) transported
      apply Fin.ext
      exact values
    have sourceRepresentativeNonSite :
        (source.frame.val.wires sourceRepresentative).scope ≠ source.site := by
      rw [sourceRepresentativeScope]
      exact regionNe
    have targetClasses :
        target.quotientWire
            (Fin.cast presentation.frameWireCountEq sourceRepresentative) =
          target.quotientWire targetWire := by
      rw [targetRepresentativeCast]
      exact (target.mem_classWires (target.quotientWire targetWire)
        targetRepresentative).1 targetMember
    have sourceClasses :
        source.quotientWire sourceRepresentative =
          source.quotientWire wire :=
      (presentation.site_local_quotients sourceRepresentative wire
        (Or.inl sourceRepresentativeNonSite)).2 targetClasses
    have coalesced := presentation.coalescedScope_eq_of_nonSite_wire
      sourceAdmissible targetAdmissible sourceRepresentative
        sourceRepresentativeNonSite
    rw [sourceClasses, targetClasses, targetScope] at coalesced
    have values :
        (Fin.cast presentation.frameRegionCountEq
          (source.coalescedScope (source.quotientWire wire))).val =
        (Fin.cast presentation.frameRegionCountEq region).val :=
      congrArg (fun index => index.val) coalesced
    apply Fin.ext
    exact values

/-- Every target quotient scoped at a regular paired region is the canonical
image of a source quotient scoped at the corresponding source region. -/
theorem quotientMap_complete_at_nonSite
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site)
    (targetQuotient : target.wireQuotient.Carrier)
    (targetScope :
      target.coalescedScope targetQuotient =
        Fin.cast presentation.frameRegionCountEq region) :
    ∃ sourceQuotient : source.wireQuotient.Carrier,
      source.coalescedScope sourceQuotient = region ∧
        presentation.quotientMap sourceQuotient = targetQuotient := by
  obtain ⟨targetWire, targetMember, targetWireScope⟩ :=
    target.coalescedScope_eq_member_scope targetQuotient
  let sourceWire :=
    Fin.cast presentation.frameWireCountEq.symm targetWire
  have targetWireCast :
      Fin.cast presentation.frameWireCountEq sourceWire = targetWire := by
    apply Fin.ext
    rfl
  have sourceWireScope :
      (source.frame.val.wires sourceWire).scope = region := by
    have transported := checkedDiagram_wire_scope_eq source.frame target.frame
      presentation.frame_eq sourceWire
    rw [targetWireCast, ← targetWireScope, targetScope] at transported
    have values :
        (Fin.cast presentation.frameRegionCountEq
          (source.frame.val.wires sourceWire).scope).val =
        (Fin.cast presentation.frameRegionCountEq region).val :=
      congrArg (fun index => index.val) transported
    apply Fin.ext
    exact values
  have sourceWireNonSite :
      (source.frame.val.wires sourceWire).scope ≠ source.site := by
    rw [sourceWireScope]
    exact regionNe
  let sourceQuotient := source.quotientWire sourceWire
  have targetClass :
      target.quotientWire
          (Fin.cast presentation.frameWireCountEq sourceWire) =
        targetQuotient := by
    rw [targetWireCast]
    exact (target.mem_classWires targetQuotient targetWire).1 targetMember
  have mapped :
      presentation.quotientMap sourceQuotient = targetQuotient := by
    rw [presentation.quotientMap_quotientWire_of_nonSite sourceWire
      sourceWireNonSite]
    exact targetClass
  have coalesced := presentation.coalescedScope_eq_of_nonSite_wire
    sourceAdmissible targetAdmissible sourceWire sourceWireNonSite
  rw [targetClass, targetScope] at coalesced
  refine ⟨sourceQuotient, ?_, mapped⟩
  have values :
      (Fin.cast presentation.frameRegionCountEq
        (source.coalescedScope sourceQuotient)).val =
      (Fin.cast presentation.frameRegionCountEq region).val :=
    congrArg (fun index => index.val) coalesced
  apply Fin.ext
  exact values

/-- The canonical quotient map is injective on every exact non-site scope. -/
theorem quotientMap_injective_at_nonSite
    (presentation : TwoInputPresentation source target)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site)
    (left right : source.wireQuotient.Carrier)
    (leftScope : source.coalescedScope left = region)
    (rightScope : source.coalescedScope right = region)
    (mapped : presentation.quotientMap left =
      presentation.quotientMap right) :
    left = right := by
  obtain ⟨leftWire, leftMember, leftWireScope⟩ :=
    source.coalescedScope_eq_member_scope left
  obtain ⟨rightWire, rightMember, rightWireScope⟩ :=
    source.coalescedScope_eq_member_scope right
  have leftClass : source.quotientWire leftWire = left :=
    (source.mem_classWires left leftWire).1 leftMember
  have rightClass : source.quotientWire rightWire = right :=
    (source.mem_classWires right rightWire).1 rightMember
  have leftNonSite :
      (source.frame.val.wires leftWire).scope ≠ source.site := by
    rw [← leftWireScope, leftScope]
    exact regionNe
  have rightNonSite :
      (source.frame.val.wires rightWire).scope ≠ source.site := by
    rw [← rightWireScope, rightScope]
    exact regionNe
  have targetClasses :
      target.quotientWire
          (Fin.cast presentation.frameWireCountEq leftWire) =
        target.quotientWire
          (Fin.cast presentation.frameWireCountEq rightWire) := by
    rw [← presentation.quotientMap_quotientWire_of_nonSite leftWire
        leftNonSite,
      ← presentation.quotientMap_quotientWire_of_nonSite rightWire
        rightNonSite,
      leftClass, rightClass]
    exact mapped
  have sourceClasses :=
    (presentation.site_local_quotients leftWire rightWire
      (Or.inl leftNonSite)).2 targetClasses
  exact leftClass.symm.trans (sourceClasses.trans rightClass)

/-- The exact quotient wires bound at paired regular frame regions are
canonically equivalent.  Site-local quotient changes cannot alter this
enumeration away from the splice site. -/
noncomputable def coalescedLocalWireEquiv
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site) :
    FiniteEquiv
      (Fin (ConcreteElaboration.exactScopeWires source.coalesceFrameRaw
        region).length)
      (Fin (ConcreteElaboration.exactScopeWires target.coalesceFrameRaw
        (Fin.cast presentation.frameRegionCountEq region)).length) :=
  listEmbeddingEquiv presentation.quotientMap
    (ConcreteElaboration.exactScopeWires source.coalesceFrameRaw region)
    (ConcreteElaboration.exactScopeWires target.coalesceFrameRaw
      (Fin.cast presentation.frameRegionCountEq region))
    (ConcreteElaboration.exactScopeWires_nodup _ _)
    (ConcreteElaboration.exactScopeWires_nodup _ _)
    (fun quotient member =>
      (ConcreteElaboration.mem_exactScopeWires _ _ _).2
        (presentation.quotientMap_coalescedScope sourceAdmissible
          targetAdmissible region regionNe quotient
          ((ConcreteElaboration.mem_exactScopeWires _ _ _).1 member)))
    (fun quotient member => by
      obtain ⟨sourceQuotient, sourceScope, mapped⟩ :=
        presentation.quotientMap_complete_at_nonSite sourceAdmissible
          targetAdmissible region regionNe quotient
          ((ConcreteElaboration.mem_exactScopeWires _ _ _).1 member)
      exact ⟨sourceQuotient,
        (ConcreteElaboration.mem_exactScopeWires _ _ _).2 sourceScope,
        mapped⟩)
    (fun left leftMember right rightMember mapped =>
      presentation.quotientMap_injective_at_nonSite region regionNe left right
        ((ConcreteElaboration.mem_exactScopeWires _ _ _).1 leftMember)
        ((ConcreteElaboration.mem_exactScopeWires _ _ _).1 rightMember)
        mapped)

theorem coalescedLocalWireEquiv_spec
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site)
    (index : Fin (ConcreteElaboration.exactScopeWires
      source.coalesceFrameRaw region).length) :
    (ConcreteElaboration.exactScopeWires target.coalesceFrameRaw
      (Fin.cast presentation.frameRegionCountEq region)).get
        (presentation.coalescedLocalWireEquiv sourceAdmissible
          targetAdmissible region regionNe index) =
      presentation.quotientMap
        ((ConcreteElaboration.exactScopeWires source.coalesceFrameRaw
          region).get index) := by
  exact listEmbeddingEquiv_spec presentation.quotientMap
    (ConcreteElaboration.exactScopeWires source.coalesceFrameRaw region)
    (ConcreteElaboration.exactScopeWires target.coalesceFrameRaw
      (Fin.cast presentation.frameRegionCountEq region))
    _ _ _ _ _ index

/-- At a proper nested splice site, a root-scoped quotient is exposed by the
ordered boundary exactly when its canonical paired quotient is exposed. -/
theorem quotientMap_mem_rootExposed_iff_of_nested
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (quotient : source.wireQuotient.Carrier)
    (sourceScope :
      source.coalescedScope quotient = source.frame.val.root) :
    quotient ∈
        (PlugLayout.coalescedOpenRoot source sourceBoundary).exposedWires ↔
      presentation.quotientMap quotient ∈
        (PlugLayout.coalescedOpenRoot target
          (presentation.targetBoundary sourceBoundary)).exposedWires := by
  have rootNe : source.frame.val.root ≠ source.site := by
    exact fun equality => hnested equality.symm
  constructor
  · intro sourceExposed
    have sourceBoundaryClass :
        quotient ∈ sourceBoundary.map source.quotientWire := by
      change quotient ∈ (sourceBoundary.map source.quotientWire).eraseDups
        at sourceExposed
      exact (List.mem_eraseDups.mp sourceExposed)
    obtain ⟨wire, wireBoundary, quotientEq⟩ :=
      List.mem_map.mp sourceBoundaryClass
    have wireNonSite : (source.frame.val.wires wire).scope ≠ source.site := by
      rw [sourceRoot wire wireBoundary]
      exact rootNe
    have targetBoundaryWire :
        Fin.cast presentation.frameWireCountEq wire ∈
          presentation.targetBoundary sourceBoundary := by
      exact List.mem_map.mpr ⟨wire, wireBoundary, rfl⟩
    have targetBoundaryClass :
        target.quotientWire (Fin.cast presentation.frameWireCountEq wire) ∈
          (presentation.targetBoundary sourceBoundary).map
            target.quotientWire :=
      List.mem_map.mpr
        ⟨Fin.cast presentation.frameWireCountEq wire, targetBoundaryWire, rfl⟩
    rw [← quotientEq,
      presentation.quotientMap_quotientWire_of_nonSite wire wireNonSite]
    change target.quotientWire
      (Fin.cast presentation.frameWireCountEq wire) ∈
        ((presentation.targetBoundary sourceBoundary).map
          target.quotientWire).eraseDups
    exact List.mem_eraseDups.mpr targetBoundaryClass
  · intro targetExposed
    have targetBoundaryClass :
        presentation.quotientMap quotient ∈
          (presentation.targetBoundary sourceBoundary).map
            target.quotientWire := by
      change presentation.quotientMap quotient ∈
          ((presentation.targetBoundary sourceBoundary).map
            target.quotientWire).eraseDups at targetExposed
      exact List.mem_eraseDups.mp targetExposed
    obtain ⟨targetWire, targetBoundaryWire, targetClassEq⟩ :=
      List.mem_map.mp targetBoundaryClass
    obtain ⟨wire, wireBoundary, wireEq⟩ :=
      List.mem_map.mp targetBoundaryWire
    subst targetWire
    let sourceClass := source.quotientWire wire
    have wireNonSite : (source.frame.val.wires wire).scope ≠ source.site := by
      rw [sourceRoot wire wireBoundary]
      exact rootNe
    have mappedSourceClass :
        presentation.quotientMap sourceClass =
          target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire) :=
      presentation.quotientMap_quotientWire_of_nonSite wire wireNonSite
    have sourceClassScope :
        source.coalescedScope sourceClass = source.frame.val.root :=
      PlugLayout.quotientWire_scope_eq_root source sourceAdmissible wire
        (sourceRoot wire wireBoundary)
    have quotientEq : quotient = sourceClass :=
      presentation.quotientMap_injective_at_nonSite source.frame.val.root
        rootNe quotient sourceClass sourceScope sourceClassScope
        (targetClassEq.symm.trans mappedSourceClass.symm)
    have sourceBoundaryClass :
        sourceClass ∈ sourceBoundary.map source.quotientWire :=
      List.mem_map.mpr ⟨wire, wireBoundary, rfl⟩
    rw [quotientEq]
    change sourceClass ∈
      (sourceBoundary.map source.quotientWire).eraseDups
    exact List.mem_eraseDups.mpr sourceBoundaryClass

/-- The coalesced exposed root classes of a proper nested paired replacement
are canonically equivalent. -/
noncomputable def coalescedRootExposedWireEquivOfNested
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root) :
    FiniteEquiv
      (Fin (PlugLayout.coalescedOpenRoot source
        sourceBoundary).exposedWires.length)
      (Fin (PlugLayout.coalescedOpenRoot target
        (presentation.targetBoundary sourceBoundary)).exposedWires.length) :=
  listEmbeddingEquiv presentation.quotientMap
    (PlugLayout.coalescedOpenRoot source sourceBoundary).exposedWires
    (PlugLayout.coalescedOpenRoot target
      (presentation.targetBoundary sourceBoundary)).exposedWires
    (PlugLayout.coalescedOpenRoot source sourceBoundary).exposedWires_nodup
    (PlugLayout.coalescedOpenRoot target
      (presentation.targetBoundary sourceBoundary)).exposedWires_nodup
    (fun quotient member => by
      have scope :=
        (PlugLayout.coalescedOpenRoot_wellFormed source sourceAdmissible
          sourceBoundary sourceRoot).exposed_root_scoped member
      exact (presentation.quotientMap_mem_rootExposed_iff_of_nested
        sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
        quotient scope).1 member)
    (fun targetQuotient member => by
      have targetBoundaryClass :
          targetQuotient ∈
            (presentation.targetBoundary sourceBoundary).map
              target.quotientWire := by
        change targetQuotient ∈
            ((presentation.targetBoundary sourceBoundary).map
              target.quotientWire).eraseDups at member
        exact List.mem_eraseDups.mp member
      obtain ⟨targetWire, targetBoundaryWire, targetClassEq⟩ :=
        List.mem_map.mp targetBoundaryClass
      obtain ⟨wire, wireBoundary, wireEq⟩ :=
        List.mem_map.mp targetBoundaryWire
      subst targetWire
      let quotient := source.quotientWire wire
      have wireNonSite :
          (source.frame.val.wires wire).scope ≠ source.site := by
        rw [sourceRoot wire wireBoundary]
        exact fun equality => hnested equality.symm
      refine ⟨quotient, ?_, ?_⟩
      · have sourceBoundaryClass :
            quotient ∈ sourceBoundary.map source.quotientWire :=
          List.mem_map.mpr ⟨wire, wireBoundary, rfl⟩
        change quotient ∈
          (sourceBoundary.map source.quotientWire).eraseDups
        exact List.mem_eraseDups.mpr sourceBoundaryClass
      · exact (presentation.quotientMap_quotientWire_of_nonSite wire
          wireNonSite).trans targetClassEq)
    (fun left leftMember right rightMember mapped => by
      have leftScope :=
        (PlugLayout.coalescedOpenRoot_wellFormed source sourceAdmissible
          sourceBoundary sourceRoot).exposed_root_scoped leftMember
      have rightScope :=
        (PlugLayout.coalescedOpenRoot_wellFormed source sourceAdmissible
          sourceBoundary sourceRoot).exposed_root_scoped rightMember
      exact presentation.quotientMap_injective_at_nonSite
        source.frame.val.root (fun equality => hnested equality.symm)
        left right leftScope rightScope mapped)

theorem coalescedRootExposedWireEquivOfNested_spec
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (index : Fin (PlugLayout.coalescedOpenRoot source
      sourceBoundary).exposedWires.length) :
    (PlugLayout.coalescedOpenRoot target
      (presentation.targetBoundary sourceBoundary)).exposedWires.get
        (presentation.coalescedRootExposedWireEquivOfNested sourceAdmissible
          targetAdmissible sourceBoundary sourceRoot hnested index) =
      presentation.quotientMap
        ((PlugLayout.coalescedOpenRoot source
          sourceBoundary).exposedWires.get index) := by
  exact listEmbeddingEquiv_spec presentation.quotientMap _ _ _ _ _ _ _ index

/-- The paired coalesced exposed-class equivalence preserves every ordered
boundary position, including repeated occurrences of the same class. -/
theorem coalescedRootExposedWireEquivOfNested_boundaryClass
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (position : Fin sourceBoundary.length) :
    presentation.coalescedRootExposedWireEquivOfNested sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested
        ((PlugLayout.coalescedOpenRoot source
          sourceBoundary).boundaryClass
          (Fin.cast (by simp [PlugLayout.coalescedOpenRoot]) position)) =
      (PlugLayout.coalescedOpenRoot target
        (presentation.targetBoundary sourceBoundary)).boundaryClass
        (Fin.cast (by simp [PlugLayout.coalescedOpenRoot,
          targetBoundary]) position) := by
  apply OpenConcreteDiagram.boundaryClass_complete
  rw [presentation.coalescedRootExposedWireEquivOfNested_spec,
    OpenConcreteDiagram.boundaryClass_sound]
  simp only [PlugLayout.coalescedOpenRoot, targetBoundary,
    List.get_eq_getElem, List.getElem_map, Function.comp_apply]
  exact presentation.quotientMap_quotientWire_of_nonSite
    (sourceBoundary.get position)
    (by
      rw [sourceRoot (sourceBoundary.get position)
        (List.get_mem sourceBoundary position)]
      exact fun equality => hnested equality.symm)

/-- The coalesced hidden root classes of a proper nested paired replacement
are canonically equivalent. -/
noncomputable def coalescedRootHiddenWireEquivOfNested
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root) :
    FiniteEquiv
      (Fin (PlugLayout.coalescedOpenRoot source
        sourceBoundary).hiddenWires.length)
      (Fin (PlugLayout.coalescedOpenRoot target
        (presentation.targetBoundary sourceBoundary)).hiddenWires.length) :=
  listEmbeddingEquiv presentation.quotientMap
    (PlugLayout.coalescedOpenRoot source sourceBoundary).hiddenWires
    (PlugLayout.coalescedOpenRoot target
      (presentation.targetBoundary sourceBoundary)).hiddenWires
    (PlugLayout.coalescedOpenRoot source sourceBoundary).hiddenWires_nodup
    (PlugLayout.coalescedOpenRoot target
      (presentation.targetBoundary sourceBoundary)).hiddenWires_nodup
    (fun quotient member => by
      have hidden :=
        (OpenConcreteDiagram.mem_hiddenWires
          (PlugLayout.coalescedOpenRoot source sourceBoundary) quotient).1
          member
      have mappedScope :=
        presentation.quotientMap_coalescedScope sourceAdmissible
          targetAdmissible source.frame.val.root
          (fun equality => hnested equality.symm) quotient hidden.1
      have targetRoot :
          Fin.cast presentation.frameRegionCountEq source.frame.val.root =
            target.frame.val.root :=
        checkedDiagram_root_eq source.frame target.frame presentation.frame_eq
      apply (OpenConcreteDiagram.mem_hiddenWires
        (PlugLayout.coalescedOpenRoot target
          (presentation.targetBoundary sourceBoundary))
        (presentation.quotientMap quotient)).2
      refine ⟨by simpa [PlugLayout.coalescedOpenRoot, targetRoot] using
        mappedScope, ?_⟩
      intro exposed
      exact hidden.2
        ((presentation.quotientMap_mem_rootExposed_iff_of_nested
          sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
          quotient hidden.1).2 exposed))
    (fun targetQuotient member => by
      have hidden :=
        (OpenConcreteDiagram.mem_hiddenWires
          (PlugLayout.coalescedOpenRoot target
            (presentation.targetBoundary sourceBoundary)) targetQuotient).1
          member
      have targetRoot :
          Fin.cast presentation.frameRegionCountEq source.frame.val.root =
            target.frame.val.root :=
        checkedDiagram_root_eq source.frame target.frame presentation.frame_eq
      have targetScope :
          target.coalescedScope targetQuotient =
            Fin.cast presentation.frameRegionCountEq source.frame.val.root := by
        simpa [PlugLayout.coalescedOpenRoot, targetRoot] using hidden.1
      obtain ⟨quotient, sourceScope, mapped⟩ :=
        presentation.quotientMap_complete_at_nonSite sourceAdmissible
          targetAdmissible source.frame.val.root
          (fun equality => hnested equality.symm) targetQuotient targetScope
      refine ⟨quotient, ?_, mapped⟩
      apply (OpenConcreteDiagram.mem_hiddenWires
        (PlugLayout.coalescedOpenRoot source sourceBoundary) quotient).2
      refine ⟨by simpa [PlugLayout.coalescedOpenRoot] using sourceScope, ?_⟩
      intro exposed
      exact hidden.2 (mapped ▸
        (presentation.quotientMap_mem_rootExposed_iff_of_nested
          sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
          quotient sourceScope).1 exposed))
    (fun left leftMember right rightMember mapped => by
      have leftScope :=
        (OpenConcreteDiagram.mem_hiddenWires
          (PlugLayout.coalescedOpenRoot source sourceBoundary) left).1
          leftMember |>.1
      have rightScope :=
        (OpenConcreteDiagram.mem_hiddenWires
          (PlugLayout.coalescedOpenRoot source sourceBoundary) right).1
          rightMember |>.1
      exact presentation.quotientMap_injective_at_nonSite
        source.frame.val.root (fun equality => hnested equality.symm)
        left right leftScope rightScope mapped)

theorem coalescedRootHiddenWireEquivOfNested_spec
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (index : Fin (PlugLayout.coalescedOpenRoot source
      sourceBoundary).hiddenWires.length) :
    (PlugLayout.coalescedOpenRoot target
      (presentation.targetBoundary sourceBoundary)).hiddenWires.get
        (presentation.coalescedRootHiddenWireEquivOfNested sourceAdmissible
          targetAdmissible sourceBoundary sourceRoot hnested index) =
      presentation.quotientMap
        ((PlugLayout.coalescedOpenRoot source
          sourceBoundary).hiddenWires.get index) := by
  exact listEmbeddingEquiv_spec presentation.quotientMap _ _ _ _ _ _ _ index

theorem target_site_ne_root_of_nested
    (presentation : TwoInputPresentation source target)
    (hnested : source.site ≠ source.frame.val.root) :
    target.site ≠ target.frame.val.root := by
  intro targetSiteRoot
  apply hnested
  apply Fin.ext
  have siteEq :
      Fin.cast presentation.frameRegionCountEq source.site = target.site :=
    presentation.site_eq
  have rootEq :
      Fin.cast presentation.frameRegionCountEq source.frame.val.root =
        target.frame.val.root :=
    checkedDiagram_root_eq source.frame target.frame presentation.frame_eq
  simpa using
    congrArg Fin.val (siteEq.trans (targetSiteRoot.trans rootEq.symm))

theorem target_site_eq_root_of_root
    (presentation : TwoInputPresentation source target)
    (hroot : source.site = source.frame.val.root) :
    target.site = target.frame.val.root := by
  have siteEq :
      Fin.cast presentation.frameRegionCountEq source.site = target.site :=
    presentation.site_eq
  have rootEq :
      Fin.cast presentation.frameRegionCountEq source.frame.val.root =
        target.frame.val.root :=
    checkedDiagram_root_eq source.frame target.frame presentation.frame_eq
  rw [hroot] at siteEq
  exact siteEq.symm.trans rootEq

/-- The actual exposed root-wire blocks of the two plugged outputs are
canonically equivalent at a proper nested replacement. -/
noncomputable def outputRootExposedWireEquivOfNested
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root) :
    FiniteEquiv
      (Fin (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).exposedWires.length)
      (Fin (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).exposedWires.length) :=
  (source.plugLayout.rootExposedWireEquiv source sourceBoundary).symm |>.trans
    ((presentation.coalescedRootExposedWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested).trans
      (target.plugLayout.rootExposedWireEquiv target
        (presentation.targetBoundary sourceBoundary)))

theorem outputRootExposedWireEquivOfNested_related
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (index : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).exposedWires.length) :
    ∃ wire : Fin source.frame.val.wireCount,
      (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).exposedWires.get index =
          source.plugLayout.frameWire (source.quotientWire wire) ∧
      (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).exposedWires.get
          (presentation.outputRootExposedWireEquivOfNested sourceAdmissible
            targetAdmissible sourceBoundary sourceRoot hnested index) =
        target.plugLayout.frameWire
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) := by
  let sourceCoalesced :=
    (source.plugLayout.rootExposedWireEquiv source sourceBoundary).symm index
  let sourceQuotient :=
    (PlugLayout.coalescedOpenRoot source sourceBoundary).exposedWires.get
      sourceCoalesced
  let wire := source.wireQuotient.origin sourceQuotient
  have sourceQuotientEq : source.quotientWire wire = sourceQuotient :=
    source.quotientWire_wireQuotient_origin sourceQuotient
  have sourceGet :
      (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).exposedWires.get index =
          source.plugLayout.frameWire sourceQuotient := by
    have mapped := source.plugLayout.rootExposedWireEquiv_spec source
      sourceBoundary sourceCoalesced
    rw [FiniteEquiv.apply_symm_apply] at mapped
    exact mapped
  refine ⟨wire, sourceGet.trans
    (congrArg source.plugLayout.frameWire sourceQuotientEq.symm), ?_⟩
  have targetCoalesced :=
    presentation.coalescedRootExposedWireEquivOfNested_spec sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested sourceCoalesced
  have targetGet := target.plugLayout.rootExposedWireEquiv_spec target
    (presentation.targetBoundary sourceBoundary)
    (presentation.coalescedRootExposedWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested sourceCoalesced)
  rw [targetCoalesced] at targetGet
  have sourceScope :=
    (PlugLayout.coalescedOpenRoot_wellFormed source sourceAdmissible
      sourceBoundary sourceRoot).exposed_root_scoped
      (List.get_mem _ sourceCoalesced)
  have sourceQuotientScope :
      source.coalescedScope sourceQuotient = source.frame.val.root := by
    simpa [PlugLayout.coalescedOpenRoot] using sourceScope
  have sourceWireScope :
      source.coalescedScope (source.quotientWire wire) =
        source.frame.val.root := by
    rw [sourceQuotientEq]
    exact sourceQuotientScope
  have mappedQuotient :
      presentation.quotientMap sourceQuotient =
        target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire) := by
    rw [← sourceQuotientEq]
    exact presentation.quotientMap_quotientWire_of_coalescedScope
      source.frame.val.root (fun equality => hnested equality.symm) wire
      sourceWireScope
  simpa [outputRootExposedWireEquivOfNested, sourceCoalesced,
    mappedQuotient] using targetGet

/-- The actual plugged-output exposed-class equivalence preserves every
ordered boundary position. -/
theorem outputRootExposedWireEquivOfNested_boundaryClass
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (position : Fin sourceBoundary.length) :
    presentation.outputRootExposedWireEquivOfNested sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested
        ((PlugLayout.outputOpenRoot source source.plugLayout
          sourceBoundary).boundaryClass
          (Fin.cast (by simp [PlugLayout.outputOpenRoot]) position)) =
      (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).boundaryClass
        (Fin.cast (by simp [PlugLayout.outputOpenRoot,
          targetBoundary]) position) := by
  let sourceCoalesced :=
    PlugLayout.coalescedOpenRoot source sourceBoundary
  let targetCoalesced :=
    PlugLayout.coalescedOpenRoot target
      (presentation.targetBoundary sourceBoundary)
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let targetBoundaryPosition :
      Fin (presentation.targetBoundary sourceBoundary).length :=
    Fin.cast (presentation.targetBoundary_length sourceBoundary).symm position
  have sourceBoundaryClass :=
    source.plugLayout.rootExposedWireEquiv_boundaryClass source sourceBoundary
      position
  have targetBoundaryClass :=
    target.plugLayout.rootExposedWireEquiv_boundaryClass target
      (presentation.targetBoundary sourceBoundary) targetBoundaryPosition
  have pairedBoundaryClass :=
    presentation.coalescedRootExposedWireEquivOfNested_boundaryClass
      sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
      position
  have sourceInverse :
      (source.plugLayout.rootExposedWireEquiv source sourceBoundary).symm
          ((PlugLayout.outputOpenRoot source source.plugLayout
            sourceBoundary).boundaryClass
            (Fin.cast (by simp [PlugLayout.outputOpenRoot]) position)) =
        (PlugLayout.coalescedOpenRoot source sourceBoundary).boundaryClass
          (Fin.cast (by simp [PlugLayout.coalescedOpenRoot]) position) := by
    rw [← sourceBoundaryClass]
    exact FiniteEquiv.symm_apply_apply _ _
  rw [outputRootExposedWireEquivOfNested, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, sourceInverse, pairedBoundaryClass]
  simpa [targetBoundaryPosition] using targetBoundaryClass

/-- The actual hidden root-wire blocks of the two plugged outputs are
canonically equivalent at a proper nested replacement. -/
noncomputable def outputRootHiddenWireEquivOfNested
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root) :
    FiniteEquiv
      (Fin (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).hiddenWires.length)
      (Fin (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).hiddenWires.length) :=
  (source.plugLayout.nestedRootHiddenWireEquiv source sourceBoundary
    hnested).symm |>.trans
      ((presentation.coalescedRootHiddenWireEquivOfNested sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested).trans
        (target.plugLayout.nestedRootHiddenWireEquiv target
          (presentation.targetBoundary sourceBoundary)
          (presentation.target_site_ne_root_of_nested hnested)))

theorem outputRootHiddenWireEquivOfNested_related
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (index : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).hiddenWires.length) :
    ∃ wire : Fin source.frame.val.wireCount,
      (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).hiddenWires.get index =
          source.plugLayout.frameWire (source.quotientWire wire) ∧
      (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).hiddenWires.get
          (presentation.outputRootHiddenWireEquivOfNested sourceAdmissible
            targetAdmissible sourceBoundary sourceRoot hnested index) =
        target.plugLayout.frameWire
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) := by
  let sourceCoalesced :=
    (source.plugLayout.nestedRootHiddenWireEquiv source sourceBoundary
      hnested).symm index
  let sourceQuotient :=
    (PlugLayout.coalescedOpenRoot source sourceBoundary).hiddenWires.get
      sourceCoalesced
  let wire := source.wireQuotient.origin sourceQuotient
  have sourceQuotientEq : source.quotientWire wire = sourceQuotient :=
    source.quotientWire_wireQuotient_origin sourceQuotient
  have sourceGet :
      (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).hiddenWires.get index =
          source.plugLayout.frameWire sourceQuotient := by
    have mapped := source.plugLayout.nestedRootHiddenWireEquiv_spec source
      sourceBoundary hnested sourceCoalesced
    rw [FiniteEquiv.apply_symm_apply] at mapped
    exact mapped
  refine ⟨wire, sourceGet.trans
    (congrArg source.plugLayout.frameWire sourceQuotientEq.symm), ?_⟩
  have targetCoalesced :=
    presentation.coalescedRootHiddenWireEquivOfNested_spec sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested sourceCoalesced
  have targetGet := target.plugLayout.nestedRootHiddenWireEquiv_spec target
    (presentation.targetBoundary sourceBoundary)
    (presentation.target_site_ne_root_of_nested hnested)
    (presentation.coalescedRootHiddenWireEquivOfNested sourceAdmissible
      targetAdmissible sourceBoundary sourceRoot hnested sourceCoalesced)
  rw [targetCoalesced] at targetGet
  have sourceScope :=
    (OpenConcreteDiagram.mem_hiddenWires
      (PlugLayout.coalescedOpenRoot source sourceBoundary) sourceQuotient).1
      (List.get_mem _ sourceCoalesced) |>.1
  have sourceQuotientScope :
      source.coalescedScope sourceQuotient = source.frame.val.root := by
    simpa [PlugLayout.coalescedOpenRoot] using sourceScope
  have sourceWireScope :
      source.coalescedScope (source.quotientWire wire) =
        source.frame.val.root := by
    rw [sourceQuotientEq]
    exact sourceQuotientScope
  have mappedQuotient :
      presentation.quotientMap sourceQuotient =
        target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire) := by
    rw [← sourceQuotientEq]
    exact presentation.quotientMap_quotientWire_of_coalescedScope
      source.frame.val.root (fun equality => hnested equality.symm) wire
      sourceWireScope
  simpa [outputRootHiddenWireEquivOfNested, sourceCoalesced,
    mappedQuotient] using targetGet

/-- The complete actual root contexts are the exposed and hidden paired
equivalences in compiler order. -/
noncomputable def outputRootWireEquivOfNested
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root) :
    FiniteEquiv
      (Fin (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).rootWires.length)
      (Fin (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).rootWires.length) :=
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let sourceEq : sourceOpen.rootWires.length =
      sourceOpen.exposedWires.length + sourceOpen.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let targetEq : targetOpen.rootWires.length =
      targetOpen.exposedWires.length + targetOpen.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  (FiniteEquiv.finCast sourceEq).trans
    ((extendWireEquiv
      (presentation.outputRootExposedWireEquivOfNested sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested)
      (presentation.outputRootHiddenWireEquivOfNested sourceAdmissible
        targetAdmissible sourceBoundary sourceRoot hnested)).trans
      (FiniteEquiv.finCast targetEq.symm))

theorem outputRootWireEquivOfNested_related
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceBoundary : List (Fin source.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (source.frame.val.wires wire).scope = source.frame.val.root)
    (hnested : source.site ≠ source.frame.val.root)
    (index : Fin (PlugLayout.outputOpenRoot source source.plugLayout
      sourceBoundary).rootWires.length) :
    ∃ wire : Fin source.frame.val.wireCount,
      (PlugLayout.outputOpenRoot source source.plugLayout
        sourceBoundary).rootWires.get index =
          source.plugLayout.frameWire (source.quotientWire wire) ∧
      (PlugLayout.outputOpenRoot target target.plugLayout
        (presentation.targetBoundary sourceBoundary)).rootWires.get
          (presentation.outputRootWireEquivOfNested sourceAdmissible
            targetAdmissible sourceBoundary sourceRoot hnested index) =
        target.plugLayout.frameWire
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)) := by
  let sourceOpen :=
    PlugLayout.outputOpenRoot source source.plugLayout sourceBoundary
  let targetOpen :=
    PlugLayout.outputOpenRoot target target.plugLayout
      (presentation.targetBoundary sourceBoundary)
  let sourceEq : sourceOpen.rootWires.length =
      sourceOpen.exposedWires.length + sourceOpen.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let targetEq : targetOpen.rootWires.length =
      targetOpen.exposedWires.length + targetOpen.hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let split := Fin.cast sourceEq index
  have indexEq : index = Fin.cast sourceEq.symm split := by
    apply Fin.ext
    rfl
  rw [indexEq]
  change ∃ wire : Fin source.frame.val.wireCount,
      sourceOpen.rootWires.get (Fin.cast sourceEq.symm split) =
          source.plugLayout.frameWire (source.quotientWire wire) ∧
      targetOpen.rootWires.get
          (Fin.cast targetEq.symm
            ((extendWireEquiv
              (presentation.outputRootExposedWireEquivOfNested
                sourceAdmissible targetAdmissible sourceBoundary sourceRoot
                hnested)
              (presentation.outputRootHiddenWireEquivOfNested
                sourceAdmissible targetAdmissible sourceBoundary sourceRoot
                hnested)) split)) =
        target.plugLayout.frameWire
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire))
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  · obtain ⟨wire, sourceGet, targetGet⟩ :=
      presentation.outputRootExposedWireEquivOfNested_related
        sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
        exposed
    refine ⟨wire, ?_, ?_⟩
    · simpa [sourceOpen, OpenConcreteDiagram.rootWires] using sourceGet
    · dsimp only [sourceOpen]
      rw [extendWireEquiv_outer]
      simpa [targetOpen, OpenConcreteDiagram.rootWires] using targetGet
  · obtain ⟨wire, sourceGet, targetGet⟩ :=
      presentation.outputRootHiddenWireEquivOfNested_related
        sourceAdmissible targetAdmissible sourceBoundary sourceRoot hnested
        hidden
    refine ⟨wire, ?_, ?_⟩
    · simpa [sourceOpen, OpenConcreteDiagram.rootWires] using sourceGet
    · dsimp only [sourceOpen]
      rw [extendWireEquiv_local]
      simpa [targetOpen, OpenConcreteDiagram.rootWires] using targetGet

/-- The actual plug-layout local wire indices at paired regular frame regions
are canonically equivalent through their retained-frame quotient classes. -/
noncomputable def regularFrameLocalWireEquiv
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site) :
    FiniteEquiv
      (Fin (ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
        (source.plugLayout.frameRegion region)).length)
      (Fin (ConcreteElaboration.exactScopeWires target.plugLayout.plugRaw
        (target.plugLayout.frameRegion
          (Fin.cast presentation.frameRegionCountEq region))).length) := by
  let targetRegion := Fin.cast presentation.frameRegionCountEq region
  have targetRegionNe : targetRegion ≠ target.site := by
    intro equality
    apply regionNe
    apply Fin.ext
    have castEquality :
        Fin.cast presentation.frameRegionCountEq region =
          Fin.cast presentation.frameRegionCountEq source.site :=
      equality.trans presentation.site_eq.symm
    exact congrArg (fun index => index.val) castEquality
  exact
    (source.plugLayout.frameLocalWireEquiv region regionNe).symm |>.trans
      ((presentation.coalescedLocalWireEquiv sourceAdmissible
        targetAdmissible region regionNe).trans
        (target.plugLayout.frameLocalWireEquiv targetRegion targetRegionNe))

theorem regularFrameLocalWireEquiv_related
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (region : Fin source.frame.val.regionCount)
    (regionNe : region ≠ source.site)
    (index : Fin (ConcreteElaboration.exactScopeWires
      source.plugLayout.plugRaw
      (source.plugLayout.frameRegion region)).length) :
    ∃ wire : Fin source.frame.val.wireCount,
      (ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
        (source.plugLayout.frameRegion region)).get index =
          source.plugLayout.frameWire (source.quotientWire wire) ∧
      (ConcreteElaboration.exactScopeWires target.plugLayout.plugRaw
        (target.plugLayout.frameRegion
          (Fin.cast presentation.frameRegionCountEq region))).get
            (presentation.regularFrameLocalWireEquiv sourceAdmissible
              targetAdmissible region regionNe index) =
          target.plugLayout.frameWire
            (target.quotientWire
              (Fin.cast presentation.frameWireCountEq wire)) := by
  let sourceEquiv := source.plugLayout.frameLocalWireEquiv region regionNe
  let sourceCoalesced := sourceEquiv.symm index
  let sourceQuotient :=
    (ConcreteElaboration.exactScopeWires source.coalesceFrameRaw region).get
      sourceCoalesced
  let wire := source.wireQuotient.origin sourceQuotient
  have sourceQuotientEq : source.quotientWire wire = sourceQuotient :=
    source.quotientWire_wireQuotient_origin sourceQuotient
  have sourceGet :
      (ConcreteElaboration.exactScopeWires source.plugLayout.plugRaw
        (source.plugLayout.frameRegion region)).get index =
        source.plugLayout.frameWire sourceQuotient := by
    have mapped := source.plugLayout.frameLocalWireEquiv_spec region regionNe
      sourceCoalesced
    rw [FiniteEquiv.apply_symm_apply] at mapped
    exact mapped
  refine ⟨wire, sourceGet.trans (congrArg source.plugLayout.frameWire
    sourceQuotientEq.symm), ?_⟩
  let targetRegion := Fin.cast presentation.frameRegionCountEq region
  have targetRegionNe : targetRegion ≠ target.site := by
    intro equality
    apply regionNe
    apply Fin.ext
    have castEquality :
        Fin.cast presentation.frameRegionCountEq region =
          Fin.cast presentation.frameRegionCountEq source.site :=
      equality.trans presentation.site_eq.symm
    exact congrArg (fun index => index.val) castEquality
  let coalescedEquiv :=
    presentation.coalescedLocalWireEquiv sourceAdmissible targetAdmissible
      region regionNe
  have targetGet :=
    target.plugLayout.frameLocalWireEquiv_spec targetRegion targetRegionNe
      (coalescedEquiv sourceCoalesced)
  have coalescedGet :
      (ConcreteElaboration.exactScopeWires target.coalesceFrameRaw
        targetRegion).get (coalescedEquiv sourceCoalesced) =
        presentation.quotientMap sourceQuotient := by
    simpa [coalescedEquiv, targetRegion, sourceQuotient] using
      presentation.coalescedLocalWireEquiv_spec sourceAdmissible
        targetAdmissible region regionNe sourceCoalesced
  rw [coalescedGet] at targetGet
  have mappedQuotient :
      presentation.quotientMap sourceQuotient =
        target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire) := by
    unfold quotientMap
    change target.quotientWire
        (Fin.cast presentation.frameWireCountEq
          (source.wireQuotient.origin sourceQuotient)) =
      target.quotientWire
        (Fin.cast presentation.frameWireCountEq wire)
    rfl
  simpa [regularFrameLocalWireEquiv, sourceEquiv, sourceCoalesced,
    coalescedEquiv, targetRegion, targetRegionNe, mappedQuotient] using targetGet

/-- Relate coalesced-host compiler indices when their quotient classes contain
corresponding copies of one retained-frame wire. -/
def coalescedContextIndexRelation
    (presentation : TwoInputPresentation source target)
    (sourceContext : ConcreteElaboration.WireContext
      source.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.coalesceFrameRaw) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length where
  Rel sourceIndex targetIndex :=
    ∃ wire : Fin source.frame.val.wireCount,
      sourceContext.get sourceIndex = source.quotientWire wire ∧
        targetContext.get targetIndex =
          target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire)

/-- Exact site contexts make the coalesced-host relation total from source to
target. -/
theorem coalescedContextIndexRelation_left_total_at_site
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceContext : ConcreteElaboration.WireContext
      source.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.coalesceFrameRaw)
    (sourceExact : sourceContext.Exact source.site)
    (targetExact : targetContext.Exact target.site)
    (sourceIndex : Fin sourceContext.length) :
    ∃ targetIndex,
      (presentation.coalescedContextIndexRelation sourceContext targetContext).Rel
        sourceIndex targetIndex := by
  let sourceClass := sourceContext.get sourceIndex
  let wire := source.wireQuotient.origin sourceClass
  have sourceClassEq : source.quotientWire wire = sourceClass :=
    source.quotientWire_wireQuotient_origin sourceClass
  have sourceVisible :
      source.coalesceFrameRaw.Encloses
        (source.coalesceFrameRaw.wires
          (source.quotientWire wire)).scope source.site := by
    rw [sourceClassEq]
    exact (sourceExact.mem_iff sourceClass).1
      (List.get_mem sourceContext sourceIndex)
  have targetVisible :
      target.coalesceFrameRaw.Encloses
        (target.coalesceFrameRaw.wires
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire))).scope
        target.site :=
    (presentation.coalescedFrame_wire_visible_at_site_iff
      sourceAdmissible targetAdmissible wire).1 sourceVisible
  have targetMember :
      target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire) ∈ targetContext :=
    (targetExact.mem_iff _).2 targetVisible
  obtain ⟨targetIndex, targetLookup⟩ :=
    targetContext.lookup?_complete targetMember
  refine ⟨targetIndex, wire, ?_, ?_⟩
  · exact sourceClassEq.symm
  · simpa only [List.get_eq_getElem] using
      ConcreteElaboration.WireContext.lookup?_sound targetLookup

/-- Exact site contexts make the coalesced-host relation total from target to
source. -/
theorem coalescedContextIndexRelation_right_total_at_site
    (presentation : TwoInputPresentation source target)
    (sourceAdmissible : source.Admissible)
    (targetAdmissible : target.Admissible)
    (sourceContext : ConcreteElaboration.WireContext
      source.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext
      target.coalesceFrameRaw)
    (sourceExact : sourceContext.Exact source.site)
    (targetExact : targetContext.Exact target.site)
    (targetIndex : Fin targetContext.length) :
    ∃ sourceIndex,
      (presentation.coalescedContextIndexRelation sourceContext targetContext).Rel
        sourceIndex targetIndex := by
  let targetClass := targetContext.get targetIndex
  let targetWire := target.wireQuotient.origin targetClass
  let wire := Fin.cast presentation.frameWireCountEq.symm targetWire
  have targetClassEq :
      target.quotientWire
          (Fin.cast presentation.frameWireCountEq wire) = targetClass := by
    have castEq :
        Fin.cast presentation.frameWireCountEq wire = targetWire := by
      apply Fin.ext
      rfl
    rw [castEq]
    exact target.quotientWire_wireQuotient_origin targetClass
  have targetVisible :
      target.coalesceFrameRaw.Encloses
        (target.coalesceFrameRaw.wires
          (target.quotientWire
            (Fin.cast presentation.frameWireCountEq wire))).scope
        target.site := by
    rw [targetClassEq]
    exact (targetExact.mem_iff targetClass).1
      (List.get_mem targetContext targetIndex)
  have sourceVisible :
      source.coalesceFrameRaw.Encloses
        (source.coalesceFrameRaw.wires
          (source.quotientWire wire)).scope source.site :=
    (presentation.coalescedFrame_wire_visible_at_site_iff
      sourceAdmissible targetAdmissible wire).2 targetVisible
  have sourceMember : source.quotientWire wire ∈ sourceContext :=
    (sourceExact.mem_iff _).2 sourceVisible
  obtain ⟨sourceIndex, sourceLookup⟩ :=
    sourceContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, wire, ?_, ?_⟩
  · simpa only [List.get_eq_getElem] using
      ConcreteElaboration.WireContext.lookup?_sound sourceLookup
  · exact targetClassEq.symm

end TwoInputPresentation

end VisualProof.Diagram.Splice.Input
