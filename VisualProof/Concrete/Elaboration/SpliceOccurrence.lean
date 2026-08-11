import VisualProof.Concrete.Elaboration.Splice

/-! Exact occurrence-stream layout for a source-derived splice. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Elaboration

namespace Splice.Input.PlugLayout

private theorem allFin_add (left right : Nat) :
    allFin (left + right) =
      (allFin left).map (Fin.castAdd right) ++
        (allFin right).map (Fin.natAdd left) := by
  simp only [allFin_eq_finRange]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.length_finRange, List.length_append, List.length_map] at hright
    simp only [List.getElem_append, List.length_map, List.length_finRange]
    split
    · simp
    · simp
      omega

private theorem filterFin_add (predicate : Fin (left + right) → Bool) :
    filterFin predicate =
      (filterFin fun index : Fin left =>
        predicate (Fin.castAdd right index)).map (Fin.castAdd right) ++
      (filterFin fun index : Fin right =>
        predicate (Fin.natAdd left index)).map (Fin.natAdd left) := by
  unfold filterFin
  rw [allFin_add]
  simp only [List.filter_append, List.filter_map]
  rfl

private theorem append_congr {left₁ left₂ right₁ right₂ : List α}
    (left : left₁ = left₂) (right : right₁ = right₂) :
    left₁ ++ right₁ = left₂ ++ right₂ := by
  rw [left, right]

private theorem map_origin_allFin (domain : SurvivorDomain size) :
    (allFin domain.count).map domain.origin = domain.enumeration := by
  rw [allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  change List.ofFn (fun index : Fin domain.enumeration.length =>
    domain.enumeration.get index) = domain.enumeration
  exact List.ofFn_getElem

private theorem map_origin_filterFin (domain : SurvivorDomain size)
    (predicate : Fin size → Bool) :
    (filterFin fun index : domain.Carrier =>
      predicate (domain.origin index)).map domain.origin =
        domain.enumeration.filter predicate := by
  unfold filterFin
  change ((allFin domain.count).filter
      (predicate ∘ domain.origin)).map domain.origin = _
  rw [← List.filter_map, map_origin_allFin]

private theorem filterFin_eq_enumeration_filter
    (domain : SurvivorDomain size) (predicate : Fin size → Bool)
    (survives : ∀ original, predicate original = true →
      domain.survives original = true) :
    filterFin predicate = domain.enumeration.filter predicate := by
  unfold SurvivorDomain.enumeration filterFin
  rw [List.filter_filter]
  apply List.filter_congr
  intro original _
  cases predicateEq : predicate original with
  | false => rfl
  | true =>
      rw [survives original predicateEq]
      rfl

@[simp] theorem mapFrameNode_region (layout : PlugLayout input)
    (node : CNode input.frame.val.regionCount) :
    (layout.mapFrameNode node).region = layout.frameRegion node.region := by
  cases node <;> rfl

@[simp] theorem mapPatternNode_region (layout : PlugLayout input)
    (node : CNode input.pattern.val.diagram.regionCount) :
    (layout.mapPatternNode node).region = layout.bodyRegion node.region := by
  cases node <;> rfl

@[simp] theorem frameRegion_eq_frameRegion_iff (layout : PlugLayout input)
    (left right : Fin input.frame.val.regionCount) :
    layout.frameRegion left = layout.frameRegion right ↔ left = right :=
  layout.frameRegion_injective.eq_iff

theorem frameRegion_ne_materialRegion (layout : PlugLayout input)
    (frame : Fin input.frame.val.regionCount)
    (material : layout.materialRegions.Carrier) :
    layout.frameRegion frame ≠ layout.materialRegion material := by
  intro equality
  have values := congrArg Fin.val equality
  simp only [PlugLayout.frameRegion, PlugLayout.materialRegion,
    Fin.val_castAdd, Fin.val_natAdd] at values
  omega

theorem materialRegion_ne_frameRegion (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (frame : Fin input.frame.val.regionCount) :
    layout.materialRegion material ≠ layout.frameRegion frame :=
  fun equality => layout.frameRegion_ne_materialRegion frame material equality.symm

theorem materialRegion_injective (layout : PlugLayout input) :
    Function.Injective layout.materialRegion := by
  intro left right equality
  apply Fin.ext
  have values := congrArg Fin.val equality
  simpa only [PlugLayout.materialRegion, Fin.val_natAdd,
    Nat.add_left_cancel_iff] using values

@[simp] theorem materialRegion_eq_materialRegion_iff
    (layout : PlugLayout input)
    (left right : layout.materialRegions.Carrier) :
    layout.materialRegion left = layout.materialRegion right ↔ left = right :=
  layout.materialRegion_injective.eq_iff

@[simp] theorem bodyRegion_eq_materialRegion_iff
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (material : layout.materialRegions.Carrier) :
    layout.bodyRegion region = layout.materialRegion material ↔
      region = layout.materialRegions.origin material := by
  unfold PlugLayout.bodyRegion
  cases indexEq : layout.materialRegions.index? region with
  | none =>
      constructor
      · intro equality
        exact (layout.frameRegion_ne_materialRegion input.site material equality).elim
      · intro equality
        subst region
        rw [layout.materialRegions.index?_origin] at indexEq
        contradiction
  | some mapped =>
      constructor
      · intro equality
        have mappedEq : mapped = material :=
          layout.materialRegion_injective equality
        subst mapped
        exact ((layout.materialRegions.index?_eq_some_iff region material).1
          indexEq).symm
      · intro equality
        subst region
        exact congrArg layout.materialRegion (Option.some.inj
          (indexEq.symm.trans
            (layout.materialRegions.index?_origin material)))

@[simp] theorem bodyRegion_eq_frameRegion_iff
    (layout : PlugLayout input)
    (patternRegion : Fin input.pattern.val.diagram.regionCount)
    (frameRegion : Fin input.frame.val.regionCount) :
    layout.bodyRegion patternRegion = layout.frameRegion frameRegion ↔
      layout.materialRegions.index? patternRegion = none ∧
        input.site = frameRegion := by
  unfold PlugLayout.bodyRegion
  cases indexEq : layout.materialRegions.index? patternRegion with
  | none => simp
  | some material =>
      simp [layout.materialRegion_ne_frameRegion]

theorem materialRegion_origin_isMaterial (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    input.binderSpine.IsMaterialRegion
      (layout.materialRegions.origin material) := by
  have survives := layout.materialRegions.origin_survives material
  rw [layout.materialRegions_exact] at survives
  exact of_decide_eq_true survives

@[simp] theorem bodyRegion_materialOrigin (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    layout.bodyRegion (layout.materialRegions.origin material) =
      layout.materialRegion material := by
  unfold PlugLayout.bodyRegion
  rw [layout.materialRegions.index?_origin]

/-- Every direct child of the terminal body has material provenance. -/
theorem directBodyChild_isMaterial (input : Input)
    (child : Fin input.pattern.val.diagram.regionCount)
    (parentEq : (input.pattern.val.diagram.regions child).parent? =
      some input.binderSpine.bodyContainer) :
    input.binderSpine.IsMaterialRegion child := by
  constructor
  · intro childRoot
    have rootSheet := input.pattern.property.diagram_well_formed.root_is_sheet
    unfold Diagram.RootIsSheet at rootSheet
    subst child
    rw [rootSheet] at parentEq
    contradiction
  · intro proxy childProxy
    have nonempty : input.binderSpine.proxyCount ≠ 0 := by
      intro empty
      have proxy' : Fin 0 := Fin.cast empty proxy
      exact Fin.elim0 proxy'
    have proxyParent := input.binderSpine.proxy_region proxy
    rw [childProxy, proxyParent] at parentEq
    simp only [CRegion.parent?, Option.some.injEq] at parentEq
    split at parentEq
    · rename_i first
      rw [input.binderSpine.body_eq_terminal_of_nonempty nonempty]
        at parentEq
      exact input.binderSpine.proxy_ne_root
        ⟨input.binderSpine.proxyCount - 1, by omega⟩ parentEq.symm
    · rename_i later
      rw [input.binderSpine.body_eq_terminal_of_nonempty nonempty]
        at parentEq
      have proxyEq := input.binderSpine.proxy_injective parentEq
      have values := congrArg Fin.val proxyEq
      simp only at values
      omega

/-- Under the terminal-body contract, a pattern node can lie outside the
material-region domain only at the designated body container. -/
theorem node_not_material_iff_bodyContainer (input : Input)
    (terminal : input.TerminalBody)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    (¬input.binderSpine.IsMaterialRegion
        (input.pattern.val.diagram.nodes node).region) ↔
      (input.pattern.val.diagram.nodes node).region =
        input.binderSpine.bodyContainer := by
  classical
  constructor
  · intro notMaterial
    let owner := (input.pattern.val.diagram.nodes node).region
    by_cases empty : input.binderSpine.proxyCount = 0
    · by_cases rootEq : owner = input.pattern.val.diagram.root
      · exact rootEq.trans
          (input.binderSpine.body_eq_root_of_empty empty).symm
      · have everyProxy : ∀ index, owner ≠ input.binderSpine.proxy index := by
          intro index
          have : False := by
            have index' : Fin 0 := Fin.cast empty index
            exact Fin.elim0 index'
          exact this.elim
        exact (notMaterial ⟨rootEq, everyProxy⟩).elim
    · have rootNe : owner ≠ input.pattern.val.diagram.root :=
        terminal.root_has_no_nodes empty node
      have notEveryProxy :
          ¬∀ index, owner ≠ input.binderSpine.proxy index := by
        intro everyProxy
        exact notMaterial ⟨rootNe, everyProxy⟩
      obtain ⟨index, ownerEq⟩ := Classical.not_forall.mp notEveryProxy
      have ownerEq' : owner = input.binderSpine.proxy index :=
        Classical.not_not.mp ownerEq
      by_cases nonterminal : index.val + 1 < input.binderSpine.proxyCount
      · exact (terminal.nonterminal_has_no_nodes index nonterminal node
          ownerEq').elim
      · let last : Fin input.binderSpine.proxyCount :=
          ⟨input.binderSpine.proxyCount - 1, by omega⟩
        have indexEq : index = last := by
          apply Fin.ext
          simp only [last]
          omega
        calc
          owner = input.binderSpine.proxy index := ownerEq'
          _ = input.binderSpine.proxy last := congrArg _ indexEq
          _ = input.binderSpine.bodyContainer :=
            (input.binderSpine.body_eq_terminal_of_nonempty empty).symm
  · intro ownerEq
    rw [ownerEq]
    exact bodyContainer_not_material input

/-- A surviving material region cannot be attached directly to the fresh root
or a nonterminal proxy.  Its only nonmaterial parent is the terminal body. -/
theorem materialChild_parent_not_material_iff_bodyContainer
    (layout : PlugLayout input) (terminal : input.TerminalBody)
    (child : layout.materialRegions.Carrier)
    (parent : Fin input.pattern.val.diagram.regionCount)
    (parentEq : (input.pattern.val.diagram.regions
      (layout.materialRegions.origin child)).parent? = some parent) :
    (¬input.binderSpine.IsMaterialRegion parent) ↔
      parent = input.binderSpine.bodyContainer := by
  classical
  have childMaterial := layout.materialRegion_origin_isMaterial child
  constructor
  · intro notMaterial
    by_cases empty : input.binderSpine.proxyCount = 0
    · by_cases rootEq : parent = input.pattern.val.diagram.root
      · exact rootEq.trans
          (input.binderSpine.body_eq_root_of_empty empty).symm
      · have everyProxy : ∀ index, parent ≠ input.binderSpine.proxy index := by
          intro index
          have : False := by
            have index' : Fin 0 := Fin.cast empty index
            exact Fin.elim0 index'
          exact this.elim
        exact (notMaterial ⟨rootEq, everyProxy⟩).elim
    · by_cases rootEq : parent = input.pattern.val.diagram.root
      · have directParent := parentEq
        rw [rootEq] at directParent
        have childEq := terminal.root_direct_child empty
          (layout.materialRegions.origin child) directParent
        exact (childMaterial.2
          ⟨0, Nat.pos_of_ne_zero empty⟩ childEq).elim
      · have notEveryProxy :
          ¬∀ index, parent ≠ input.binderSpine.proxy index := by
          intro everyProxy
          exact notMaterial ⟨rootEq, everyProxy⟩
        obtain ⟨index, parentNe⟩ := Classical.not_forall.mp notEveryProxy
        have parentProxy : parent = input.binderSpine.proxy index :=
          Classical.not_not.mp parentNe
        by_cases nonterminal :
            index.val + 1 < input.binderSpine.proxyCount
        · have directParent := parentEq
          rw [parentProxy] at directParent
          have childEq := terminal.nonterminal_direct_child index nonterminal
            (layout.materialRegions.origin child) directParent
          exact (childMaterial.2
            ⟨index.val + 1, nonterminal⟩ childEq).elim
        · let last : Fin input.binderSpine.proxyCount :=
            ⟨input.binderSpine.proxyCount - 1, by omega⟩
          have indexEq : index = last := by
            apply Fin.ext
            simp only [last]
            omega
          calc
            parent = input.binderSpine.proxy index := parentProxy
            _ = input.binderSpine.proxy last := congrArg _ indexEq
            _ = input.binderSpine.bodyContainer :=
              (input.binderSpine.body_eq_terminal_of_nonempty empty).symm
  · intro parentBody
    rw [parentBody]
    exact bodyContainer_not_material input

@[simp] theorem node_materialIndex_eq_none_iff_bodyContainer
    (layout : PlugLayout input) (terminal : input.TerminalBody)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    layout.materialRegions.index?
        (input.pattern.val.diagram.nodes node).region = none ↔
      (input.pattern.val.diagram.nodes node).region =
        input.binderSpine.bodyContainer := by
  rw [layout.materialRegions.index?_eq_none_iff,
    layout.materialRegions_exact]
  simpa using node_not_material_iff_bodyContainer input terminal node

@[simp] theorem materialChild_parentIndex_eq_none_iff_bodyContainer
    (layout : PlugLayout input) (terminal : input.TerminalBody)
    (child : layout.materialRegions.Carrier)
    (parent : Fin input.pattern.val.diagram.regionCount)
    (parentEq : (input.pattern.val.diagram.regions
      (layout.materialRegions.origin child)).parent? = some parent) :
    layout.materialRegions.index? parent = none ↔
      parent = input.binderSpine.bodyContainer := by
  rw [layout.materialRegions.index?_eq_none_iff,
    layout.materialRegions_exact]
  simpa using layout.materialChild_parent_not_material_iff_bodyContainer
    terminal child parent parentEq

@[simp] theorem patternNode_bodyRegion_eq_frameRegion_iff
    (layout : PlugLayout input) (terminal : input.TerminalBody)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (region : Fin input.frame.val.regionCount) :
    layout.bodyRegion (input.pattern.val.diagram.nodes node).region =
        layout.frameRegion region ↔
      (input.pattern.val.diagram.nodes node).region =
          input.binderSpine.bodyContainer ∧
        input.site = region := by
  rw [bodyRegion_eq_frameRegion_iff,
    layout.node_materialIndex_eq_none_iff_bodyContainer terminal node]

@[simp] theorem materialChild_parent_eq_some_frameRegion_iff
    (layout : PlugLayout input) (terminal : input.TerminalBody)
    (child : layout.materialRegions.Carrier)
    (region : Fin input.frame.val.regionCount) :
    (layout.mapPatternRegion (input.pattern.val.diagram.regions
      (layout.materialRegions.origin child))).parent? =
        some (layout.frameRegion region) ↔
      (input.pattern.val.diagram.regions
        (layout.materialRegions.origin child)).parent? =
          some input.binderSpine.bodyContainer ∧
        input.site = region := by
  generalize regionEq : input.pattern.val.diagram.regions
    (layout.materialRegions.origin child) = sourceRegion
  cases sourceRegion with
  | sheet =>
      have rootEq := input.pattern.property.diagram_well_formed.only_root_is_sheet
        (layout.materialRegions.origin child) regionEq
      exact (layout.materialRegion_origin_isMaterial child).1 rootEq |>.elim
  | cut parent =>
      have parentEq : (input.pattern.val.diagram.regions
          (layout.materialRegions.origin child)).parent? = some parent := by
        rw [regionEq]
        rfl
      simp only [PlugLayout.mapPatternRegion, CRegion.parent?,
        Option.some.injEq]
      rw [bodyRegion_eq_frameRegion_iff,
        layout.materialChild_parentIndex_eq_none_iff_bodyContainer
          terminal child parent parentEq]
  | bubble parent arity =>
      have parentEq : (input.pattern.val.diagram.regions
          (layout.materialRegions.origin child)).parent? = some parent := by
        rw [regionEq]
        rfl
      simp only [PlugLayout.mapPatternRegion, CRegion.parent?,
        Option.some.injEq]
      rw [bodyRegion_eq_frameRegion_iff,
        layout.materialChild_parentIndex_eq_none_iff_bodyContainer
          terminal child parent parentEq]

theorem mapPatternRegion_parent_frameRegion_site_eq
    (layout : PlugLayout input)
    (sourceRegion : CRegion input.pattern.val.diagram.regionCount)
    (region : Fin input.frame.val.regionCount)
    (parentEq : (layout.mapPatternRegion sourceRegion).parent? =
      some (layout.frameRegion region)) :
    input.site = region := by
  cases sourceRegion with
  | sheet =>
      simp only [PlugLayout.mapPatternRegion, CRegion.parent?,
        Option.some.injEq] at parentEq
      exact layout.frameRegion_injective parentEq
  | cut parent =>
      simp only [PlugLayout.mapPatternRegion, CRegion.parent?,
        Option.some.injEq] at parentEq
      exact (layout.bodyRegion_eq_frameRegion_iff parent region).1 parentEq |>.2
  | bubble parent arity =>
      simp only [PlugLayout.mapPatternRegion, CRegion.parent?,
        Option.some.injEq] at parentEq
      exact (layout.bodyRegion_eq_frameRegion_iff parent region).1 parentEq |>.2

@[simp] theorem mapFrameRegion_parent_eq_some_iff
    (layout : PlugLayout input)
    (child : Fin input.frame.val.regionCount)
    (region : Fin input.frame.val.regionCount) :
    (layout.mapFrameRegion (input.frame.val.regions child)).parent? =
        some (layout.frameRegion region) ↔
      (input.frame.val.regions child).parent? = some region := by
  cases input.frame.val.regions child <;>
    simp [PlugLayout.mapFrameRegion, CRegion.parent?]

@[simp] theorem mapPatternRegion_parent_eq_some_material_iff
    (layout : PlugLayout input)
    (child : layout.materialRegions.Carrier)
    (material : layout.materialRegions.Carrier) :
    (layout.mapPatternRegion (input.pattern.val.diagram.regions
      (layout.materialRegions.origin child))).parent? =
        some (layout.materialRegion material) ↔
      (input.pattern.val.diagram.regions
        (layout.materialRegions.origin child)).parent? =
          some (layout.materialRegions.origin material) := by
  cases input.pattern.val.diagram.regions
      (layout.materialRegions.origin child) <;>
    simp [PlugLayout.mapPatternRegion, CRegion.parent?,
      frameRegion_ne_materialRegion]

/-- Frame-node occurrences retained at a frame region. -/
def frameNodeOccurrences (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    List (LocalOccurrence layout.regionCount layout.nodeCount) :=
  (filterFin fun node : Fin input.frame.val.nodeCount =>
    decide ((input.frame.val.nodes node).region = region)).map fun node =>
      .node (layout.frameNode node)

/-- Pattern-node occurrences whose mapped owner is a given frame region. -/
def patternNodeOccurrences (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    List (LocalOccurrence layout.regionCount layout.nodeCount) :=
  (filterFin fun node : Fin input.pattern.val.diagram.nodeCount =>
    decide (layout.bodyRegion
      (input.pattern.val.diagram.nodes node).region =
        layout.frameRegion region)).map fun node =>
      .node (layout.patternNode node)

/-- Frame-child occurrences retained at a frame region. -/
def frameChildOccurrences (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    List (LocalOccurrence layout.regionCount layout.nodeCount) :=
  (filterFin fun child : Fin input.frame.val.regionCount =>
    decide ((input.frame.val.regions child).parent? = some region)).map fun child =>
      .child (layout.frameRegion child)

/-- Source-frame occurrence transport into the retained target blocks. -/
def mapFrameOccurrence (layout : PlugLayout input) :
    LocalOccurrence input.frame.val.regionCount input.frame.val.nodeCount →
      LocalOccurrence layout.regionCount layout.nodeCount
  | .node node => .node (layout.frameNode node)
  | .child child => .child (layout.frameRegion child)

/-- Pattern occurrence transport at the terminal body. -/
def mapPatternOccurrence (layout : PlugLayout input) :
    LocalOccurrence input.pattern.val.diagram.regionCount
        input.pattern.val.diagram.nodeCount →
      LocalOccurrence layout.regionCount layout.nodeCount
  | .node node => .node (layout.patternNode node)
  | .child child => .child (layout.bodyRegion child)

/-- Mapping the source frame's local occurrence stream produces exactly the
retained node and child blocks. -/
theorem map_localOccurrences_frame (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    (localOccurrences input.frame.val region).map layout.mapFrameOccurrence =
      layout.frameNodeOccurrences region ++
        layout.frameChildOccurrences region := by
  unfold localOccurrences mapFrameOccurrence frameNodeOccurrences
    frameChildOccurrences
  simp only [List.map_append, List.map_map]
  rfl

/-- Surviving material-child occurrences whose mapped parent is a given frame
region. -/
def materialChildOccurrences (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    List (LocalOccurrence layout.regionCount layout.nodeCount) :=
  (filterFin fun child : layout.materialRegions.Carrier =>
    decide ((layout.mapPatternRegion (input.pattern.val.diagram.regions
      (layout.materialRegions.origin child))).parent? =
        some (layout.frameRegion region))).map fun child =>
      .child (layout.materialRegion child)

/-- Pattern nodes retained in one material region. -/
def materialNodeOccurrences (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    List (LocalOccurrence layout.regionCount layout.nodeCount) :=
  (filterFin fun node : Fin input.pattern.val.diagram.nodeCount =>
    decide ((input.pattern.val.diagram.nodes node).region =
      layout.materialRegions.origin material)).map fun node =>
        .node (layout.patternNode node)

/-- Pattern child regions retained directly inside one material region. -/
def materialRegionChildOccurrences (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    List (LocalOccurrence layout.regionCount layout.nodeCount) :=
  (filterFin fun child : layout.materialRegions.Carrier =>
    decide ((input.pattern.val.diagram.regions
      (layout.materialRegions.origin child)).parent? =
        some (layout.materialRegions.origin material))).map fun child =>
          .child (layout.materialRegion child)

/-- Pattern nodes owned by the designated terminal body. -/
def bodyNodeOccurrences (layout : PlugLayout input) :
    List (LocalOccurrence layout.regionCount layout.nodeCount) :=
  (filterFin fun node : Fin input.pattern.val.diagram.nodeCount =>
    decide ((input.pattern.val.diagram.nodes node).region =
      input.binderSpine.bodyContainer)).map fun node =>
        .node (layout.patternNode node)

/-- Surviving material children directly owned by the designated terminal
body. -/
def bodyChildOccurrences (layout : PlugLayout input) :
    List (LocalOccurrence layout.regionCount layout.nodeCount) :=
  (filterFin fun child : layout.materialRegions.Carrier =>
    decide ((input.pattern.val.diagram.regions
      (layout.materialRegions.origin child)).parent? =
        some input.binderSpine.bodyContainer)).map fun child =>
          .child (layout.materialRegion child)

/-- Direct source body children and their dense material target identifiers
are the same stable occurrence stream. -/
theorem map_directBodyChildren (layout : PlugLayout input) :
    (filterFin fun child : Fin input.pattern.val.diagram.regionCount =>
      decide ((input.pattern.val.diagram.regions child).parent? =
        some input.binderSpine.bodyContainer)).map (fun child =>
          (LocalOccurrence.child (layout.bodyRegion child) :
            LocalOccurrence layout.regionCount layout.nodeCount)) =
      layout.bodyChildOccurrences := by
  let predicate : Fin input.pattern.val.diagram.regionCount → Bool :=
    fun child => decide ((input.pattern.val.diagram.regions child).parent? =
      some input.binderSpine.bodyContainer)
  have survives : ∀ child, predicate child = true →
      layout.materialRegions.survives child = true := by
    intro child accepted
    rw [layout.materialRegions_exact]
    apply decide_eq_true
    apply directBodyChild_isMaterial input child
    exact of_decide_eq_true accepted
  have sourceFilter := filterFin_eq_enumeration_filter
    layout.materialRegions predicate survives
  have mappedOrigins := map_origin_filterFin
    layout.materialRegions predicate
  have origins :
      filterFin predicate =
        (filterFin fun child : layout.materialRegions.Carrier =>
          predicate (layout.materialRegions.origin child)).map
            layout.materialRegions.origin :=
    sourceFilter.trans mappedOrigins.symm
  have occurrences := congrArg
    (List.map fun child =>
      (LocalOccurrence.child (layout.bodyRegion child) :
        LocalOccurrence layout.regionCount layout.nodeCount)) origins
  unfold bodyChildOccurrences
  simpa only [predicate, List.map_map, Function.comp_def,
    bodyRegion_materialOrigin] using occurrences

/-- Mapping the source terminal body's direct occurrence stream gives exactly
the inserted node and material-child blocks. -/
theorem map_localOccurrences_body (layout : PlugLayout input) :
    (localOccurrences input.pattern.val.diagram
      input.binderSpine.bodyContainer).map layout.mapPatternOccurrence =
        layout.bodyNodeOccurrences ++ layout.bodyChildOccurrences := by
  unfold localOccurrences mapPatternOccurrence bodyNodeOccurrences
  simp only [List.map_append, List.map_map]
  change
    (filterFin fun node : Fin input.pattern.val.diagram.nodeCount =>
      decide ((input.pattern.val.diagram.nodes node).region =
        input.binderSpine.bodyContainer)).map (fun node =>
          (LocalOccurrence.node (layout.patternNode node) :
            LocalOccurrence layout.regionCount layout.nodeCount)) ++
    (filterFin fun child : Fin input.pattern.val.diagram.regionCount =>
      decide ((input.pattern.val.diagram.regions child).parent? =
        some input.binderSpine.bodyContainer)).map (fun child =>
          (LocalOccurrence.child (layout.bodyRegion child) :
            LocalOccurrence layout.regionCount layout.nodeCount)) = _
  rw [layout.map_directBodyChildren]

theorem patternNodeOccurrences_eq_nil_of_ne_site
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) (notSite : region ≠ input.site) :
    layout.patternNodeOccurrences region = [] := by
  unfold patternNodeOccurrences
  have filtered :
      (filterFin fun node : Fin input.pattern.val.diagram.nodeCount =>
        decide (layout.bodyRegion
          (input.pattern.val.diagram.nodes node).region =
            layout.frameRegion region)) = [] := by
    unfold filterFin
    apply List.filter_eq_nil_iff.2
    intro node _ accepted
    have mapped := of_decide_eq_true accepted
    have siteEq := (layout.bodyRegion_eq_frameRegion_iff
      (input.pattern.val.diagram.nodes node).region region).1 mapped |>.2
    exact notSite siteEq.symm
  rw [filtered]
  rfl

theorem materialChildOccurrences_eq_nil_of_ne_site
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) (notSite : region ≠ input.site) :
    layout.materialChildOccurrences region = [] := by
  unfold materialChildOccurrences
  have filtered :
      (filterFin fun child : layout.materialRegions.Carrier =>
        decide ((layout.mapPatternRegion (input.pattern.val.diagram.regions
          (layout.materialRegions.origin child))).parent? =
            some (layout.frameRegion region))) = [] := by
    unfold filterFin
    apply List.filter_eq_nil_iff.2
    intro child _ accepted
    apply notSite
    exact layout.mapPatternRegion_parent_frameRegion_site_eq
      (input.pattern.val.diagram.regions
        (layout.materialRegions.origin child)) region
      (of_decide_eq_true accepted) |>.symm
  rw [filtered]
  rfl

theorem patternNodeOccurrences_site (layout : PlugLayout input)
    (admissible : input.Admissible) :
    layout.patternNodeOccurrences input.site =
      layout.bodyNodeOccurrences := by
  unfold patternNodeOccurrences bodyNodeOccurrences
  apply congrArg (List.map fun node =>
    (LocalOccurrence.node (layout.patternNode node) :
      LocalOccurrence layout.regionCount layout.nodeCount))
  apply List.filter_congr
  intro node _
  simp only [layout.patternNode_bodyRegion_eq_frameRegion_iff
    admissible.terminal_body node input.site, and_true]

theorem materialChildOccurrences_site (layout : PlugLayout input)
    (admissible : input.Admissible) :
    layout.materialChildOccurrences input.site =
      layout.bodyChildOccurrences := by
  unfold materialChildOccurrences bodyChildOccurrences
  apply congrArg (List.map fun child =>
    (LocalOccurrence.child (layout.materialRegion child) :
      LocalOccurrence layout.regionCount layout.nodeCount))
  apply List.filter_congr
  intro child _
  simp only [layout.materialChild_parent_eq_some_frameRegion_iff
    admissible.terminal_body child input.site, and_true]

/-- Exact compiler traversal order at every retained frame region: retained
nodes, inserted nodes, retained children, then surviving material children. -/
theorem localOccurrences_frameRegion (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    localOccurrences layout.plugRaw (layout.frameRegion region) =
      (layout.frameNodeOccurrences region ++
        layout.patternNodeOccurrences region) ++
      (layout.frameChildOccurrences region ++
        layout.materialChildOccurrences region) := by
  unfold localOccurrences frameNodeOccurrences patternNodeOccurrences
    frameChildOccurrences materialChildOccurrences
  simp only [PlugLayout.plugRaw, PlugLayout.nodeCount, PlugLayout.regionCount]
  rw [filterFin_add, filterFin_add]
  simp only [List.map_append, List.map_map]
  have frameNodes :
      (filterFin fun index : Fin input.frame.val.nodeCount =>
        decide ((layout.plugNode
          (Fin.castAdd input.pattern.val.diagram.nodeCount index)).region =
            layout.frameRegion region)) =
      filterFin fun node =>
        decide ((input.frame.val.nodes node).region = region) := by
    apply List.filter_congr
    intro node _
    simp only [PlugLayout.plugNode, Fin.addCases_left,
      mapFrameNode_region, frameRegion_eq_frameRegion_iff]
  have patternNodes :
      (filterFin fun index : Fin input.pattern.val.diagram.nodeCount =>
        decide ((layout.plugNode
          (Fin.natAdd input.frame.val.nodeCount index)).region =
            layout.frameRegion region)) =
      filterFin fun node =>
        decide (layout.bodyRegion
          (input.pattern.val.diagram.nodes node).region =
            layout.frameRegion region) := by
    apply List.filter_congr
    intro node _
    simp only [PlugLayout.plugNode, Fin.addCases_right,
      mapPatternNode_region]
  have frameChildren :
      (filterFin fun index : Fin input.frame.val.regionCount =>
        decide ((layout.plugRegion
          (Fin.castAdd layout.materialRegions.count index)).parent? =
            some (layout.frameRegion region))) =
      filterFin fun child =>
        decide ((input.frame.val.regions child).parent? = some region) := by
    apply List.filter_congr
    intro child _
    simp only [PlugLayout.plugRegion, Fin.addCases_left,
      mapFrameRegion_parent_eq_some_iff]
  have materialChildren :
      (filterFin fun index : layout.materialRegions.Carrier =>
        decide ((layout.plugRegion
          (Fin.natAdd input.frame.val.regionCount index)).parent? =
            some (layout.frameRegion region))) =
      filterFin fun child =>
        decide ((layout.mapPatternRegion
          (input.pattern.val.diagram.regions
            (layout.materialRegions.origin child))).parent? =
              some (layout.frameRegion region)) := by
    apply List.filter_congr
    intro child _
    simp only [PlugLayout.plugRegion, Fin.addCases_right]
  have frameNodeBlock := congrArg
    (List.map (fun node =>
      (LocalOccurrence.node (layout.frameNode node) :
        LocalOccurrence layout.regionCount layout.nodeCount))) frameNodes
  have patternNodeBlock := congrArg
    (List.map (fun node =>
      (LocalOccurrence.node (layout.patternNode node) :
        LocalOccurrence layout.regionCount layout.nodeCount))) patternNodes
  have frameChildBlock := congrArg
    (List.map (fun child =>
      (LocalOccurrence.child (layout.frameRegion child) :
        LocalOccurrence layout.regionCount layout.nodeCount))) frameChildren
  have materialChildBlock := congrArg
    (List.map (fun child =>
      (LocalOccurrence.child (layout.materialRegion child) :
        LocalOccurrence layout.regionCount layout.nodeCount))) materialChildren
  have blocks := append_congr
    (append_congr frameNodeBlock patternNodeBlock)
    (append_congr frameChildBlock materialChildBlock)
  simpa only [PlugLayout.frameNode, PlugLayout.patternNode,
    PlugLayout.frameRegion, PlugLayout.materialRegion]
    using blocks

/-- Away from the splice site, the target compiler sees exactly the mapped
source-frame occurrence stream and no pattern occurrences. -/
theorem localOccurrences_frameRegion_of_ne_site
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) (notSite : region ≠ input.site) :
    localOccurrences layout.plugRaw (layout.frameRegion region) =
      (localOccurrences input.frame.val region).map layout.mapFrameOccurrence := by
  rw [layout.localOccurrences_frameRegion region,
    layout.patternNodeOccurrences_eq_nil_of_ne_site region notSite,
    layout.materialChildOccurrences_eq_nil_of_ne_site region notSite]
  simp only [List.append_nil]
  exact (layout.map_localOccurrences_frame region).symm

/-- At the splice site, the target traversal contains the retained source
blocks and exactly the direct terminal-body blocks. -/
theorem localOccurrences_site (layout : PlugLayout input)
    (admissible : input.Admissible) :
    localOccurrences layout.plugRaw (layout.frameRegion input.site) =
      (layout.frameNodeOccurrences input.site ++
        layout.bodyNodeOccurrences) ++
      (layout.frameChildOccurrences input.site ++
        layout.bodyChildOccurrences) := by
  rw [layout.localOccurrences_frameRegion input.site,
    layout.patternNodeOccurrences_site admissible,
    layout.materialChildOccurrences_site admissible]

/-- Every material target region has exactly the source pattern occurrences
owned directly by its source region, in compiler order. -/
theorem localOccurrences_materialRegion (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    localOccurrences layout.plugRaw (layout.materialRegion material) =
      layout.materialNodeOccurrences material ++
        layout.materialRegionChildOccurrences material := by
  unfold localOccurrences materialNodeOccurrences
    materialRegionChildOccurrences
  simp only [PlugLayout.plugRaw, PlugLayout.nodeCount, PlugLayout.regionCount]
  rw [filterFin_add, filterFin_add]
  simp only [List.map_append, List.map_map]
  have noFrameNodes :
      (filterFin fun index : Fin input.frame.val.nodeCount =>
        decide ((layout.plugNode
          (Fin.castAdd input.pattern.val.diagram.nodeCount index)).region =
            layout.materialRegion material)) = [] := by
    unfold filterFin
    apply List.filter_eq_nil_iff.2
    intro node _
    simp only [PlugLayout.plugNode, Fin.addCases_left,
      mapFrameNode_region]
    simpa using layout.frameRegion_ne_materialRegion
      (input.frame.val.nodes node).region material
  have patternNodes :
      (filterFin fun index : Fin input.pattern.val.diagram.nodeCount =>
        decide ((layout.plugNode
          (Fin.natAdd input.frame.val.nodeCount index)).region =
            layout.materialRegion material)) =
      filterFin fun node =>
        decide ((input.pattern.val.diagram.nodes node).region =
          layout.materialRegions.origin material) := by
    apply List.filter_congr
    intro node _
    simp only [PlugLayout.plugNode, Fin.addCases_right,
      mapPatternNode_region, bodyRegion_eq_materialRegion_iff]
  have noFrameChildren :
      (filterFin fun index : Fin input.frame.val.regionCount =>
        decide ((layout.plugRegion
          (Fin.castAdd layout.materialRegions.count index)).parent? =
            some (layout.materialRegion material))) = [] := by
    unfold filterFin
    apply List.filter_eq_nil_iff.2
    intro child _
    simp only [PlugLayout.plugRegion, Fin.addCases_left]
    cases input.frame.val.regions child <;>
      simp [PlugLayout.mapFrameRegion, CRegion.parent?,
        frameRegion_ne_materialRegion]
  have materialChildren :
      (filterFin fun index : layout.materialRegions.Carrier =>
        decide ((layout.plugRegion
          (Fin.natAdd input.frame.val.regionCount index)).parent? =
            some (layout.materialRegion material))) =
      filterFin fun child =>
        decide ((input.pattern.val.diagram.regions
          (layout.materialRegions.origin child)).parent? =
            some (layout.materialRegions.origin material)) := by
    apply List.filter_congr
    intro child _
    simp only [PlugLayout.plugRegion, Fin.addCases_right,
      mapPatternRegion_parent_eq_some_material_iff]
  have noFrameNodeBlock := congrArg
    (List.map (fun node =>
      (LocalOccurrence.node (layout.frameNode node) :
        LocalOccurrence layout.regionCount layout.nodeCount))) noFrameNodes
  have patternNodeBlock := congrArg
    (List.map (fun node =>
      (LocalOccurrence.node (layout.patternNode node) :
        LocalOccurrence layout.regionCount layout.nodeCount))) patternNodes
  have noFrameChildBlock := congrArg
    (List.map (fun child =>
      (LocalOccurrence.child (layout.frameRegion child) :
        LocalOccurrence layout.regionCount layout.nodeCount))) noFrameChildren
  have materialChildBlock := congrArg
    (List.map (fun child =>
      (LocalOccurrence.child (layout.materialRegion child) :
        LocalOccurrence layout.regionCount layout.nodeCount))) materialChildren
  have blocks := append_congr
    (append_congr noFrameNodeBlock patternNodeBlock)
    (append_congr noFrameChildBlock materialChildBlock)
  simpa only [PlugLayout.frameNode, PlugLayout.patternNode,
    PlugLayout.frameRegion, PlugLayout.materialRegion, List.map_nil,
    List.nil_append] using blocks

end Splice.Input.PlugLayout

end VisualProof.Concrete
