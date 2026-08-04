import VisualProof.Rule.Soundness.Iteration.SameSite

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

private theorem filterMap_nodup_of_some_injective
    {values : List α} {f : α → Option β}
    (hnodup : values.Nodup)
    (hinjective : ∀ {first second mapped},
      f first = some mapped → f second = some mapped → first = second) :
    (values.filterMap f).Nodup := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at hnodup
      rcases hnodup with ⟨hhead, htail⟩
      cases hmapped : f head with
      | none => simpa [List.filterMap, hmapped] using ih htail
      | some mapped =>
          rw [show (head :: tail).filterMap f =
              mapped :: tail.filterMap f by simp [List.filterMap, hmapped],
            List.nodup_cons]
          constructor
          · intro hmember
            obtain ⟨other, hother, hotherMapped⟩ :=
              List.mem_filterMap.mp hmember
            exact hhead (by
              rw [hinjective hmapped hotherMapped]
              exact hother)
          · exact ih htail

private theorem selection_anchor_not_selected
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    ¬ selection.val.SelectsRegion selection.val.anchor := by
  rintro ⟨root, hroot, hencloses⟩
  exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
    input.property (selection.property.childRoots_direct root hroot))
    hencloses

def deiterationDomains
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    FrameDomains input.val selection := {}

theorem deiterationJustifierAnchor_not_selected
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    witness.justifier.val.anchor ∉ selection.selectedRegions := by
  intro selected
  have selects : selection.val.SelectsRegion witness.justifier.val.anchor :=
    (selection.mem_selectedRegions witness.justifier.val.anchor).1 selected
  have selectsAnchor := SelectionRequest.SelectsRegion.downward input.property
    selects witness.ancestor
  exact selection_anchor_not_selected input selection selectsAnchor

theorem deiterationJustifierAnchor_survives
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationDomains input selection).regions.survives
        witness.justifier.val.anchor = true := by
  apply ((deiterationDomains input selection).region_survives_iff _).2
  exact Or.inr (deiterationJustifierAnchor_not_selected input selection witness)

theorem deiterationJustifierRegion_survives
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {region : Fin input.val.regionCount}
    (selected : region ∈ witness.justifier.selectedRegions) :
    (deiterationDomains input selection).regions.survives region = true := by
  apply ((deiterationDomains input selection).region_survives_iff _).2
  exact Or.inr (witness.regions_disjoint region selected)

theorem deiterationJustifierNode_survives
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {node : Fin input.val.nodeCount}
    (selected : node ∈ witness.justifier.selectedNodes) :
    (deiterationDomains input selection).nodes.survives node = true := by
  apply ((deiterationDomains input selection).node_survives_iff _).2
  exact witness.nodes_disjoint node selected

theorem deiterationJustifierWire_survives
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {wire : Fin input.val.wireCount}
    (selected : wire ∈ witness.justifier.internalWires) :
    (deiterationDomains input selection).wires.survives wire = true := by
  apply ((deiterationDomains input selection).wire_survives_iff _).2
  exact witness.internalWires_disjoint wire selected

def deiterationRetainedRequest
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    SelectionRequest
      (input.val.removeRaw selection (deiterationDomains input selection)) where
  anchor := (deiterationDomains input selection).regions.index
    witness.justifier.val.anchor
    (deiterationJustifierAnchor_survives input selection witness)
  childRoots := witness.justifier.val.childRoots.filterMap
    (deiterationDomains input selection).regions.index?
  directNodes := witness.justifier.val.directNodes.filterMap
    (deiterationDomains input selection).nodes.index?
  explicitWires := witness.justifier.val.explicitWires.filterMap
    (deiterationDomains input selection).wires.index?

private theorem deiterationRetainedRequest_childRoot_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {mapped : Fin (deiterationDomains input selection).regions.count}
    (member : mapped ∈
      (deiterationRetainedRequest input selection witness).childRoots) :
    (deiterationDomains input selection).regions.origin mapped ∈
      witness.justifier.val.childRoots := by
  obtain ⟨original, originalMember, mappedEq⟩ :=
    List.mem_filterMap.mp member
  have origin := ((deiterationDomains input selection).regions
    |>.index?_eq_some_iff original mapped).1 mappedEq
  rw [origin]
  exact originalMember

private theorem deiterationRetainedRequest_directNode_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {mapped : Fin (deiterationDomains input selection).nodes.count}
    (member : mapped ∈
      (deiterationRetainedRequest input selection witness).directNodes) :
    (deiterationDomains input selection).nodes.origin mapped ∈
      witness.justifier.val.directNodes := by
  obtain ⟨original, originalMember, mappedEq⟩ :=
    List.mem_filterMap.mp member
  have origin := ((deiterationDomains input selection).nodes
    |>.index?_eq_some_iff original mapped).1 mappedEq
  rw [origin]
  exact originalMember

private theorem deiterationRetainedRequest_explicitWire_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {mapped : Fin (deiterationDomains input selection).wires.count}
    (member : mapped ∈
      (deiterationRetainedRequest input selection witness).explicitWires) :
    (deiterationDomains input selection).wires.origin mapped ∈
      witness.justifier.val.explicitWires := by
  obtain ⟨original, originalMember, mappedEq⟩ :=
    List.mem_filterMap.mp member
  have origin := ((deiterationDomains input selection).wires
    |>.index?_eq_some_iff original mapped).1 mappedEq
  rw [origin]
  exact originalMember

private theorem survivorIndex_eq_of_eq
    (domain : SurvivorDomain size) {first second : Fin size}
    (equality : first = second)
    (firstSurvives : domain.survives first = true)
    (secondSurvives : domain.survives second = true) :
    domain.index first firstSurvives = domain.index second secondSurvives := by
  subst second
  rfl

private theorem removeRaw_parent_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    {child parent : domains.regions.Carrier}
    (hparent : ((input.val.removeRaw selection domains).regions child).parent? =
      some parent) :
    (input.val.regions (domains.regions.origin child)).parent? =
      some (domains.regions.origin parent) := by
  change ((domains.regions.reindexRegion?
    (input.val.regions (domains.regions.origin child))).getD .sheet).parent? =
      some parent at hparent
  cases hkind : input.val.regions (domains.regions.origin child) with
  | sheet =>
      rw [hkind] at hparent
      change none = some parent at hparent
      contradiction
  | cut originalParent =>
      have originalParentSurvives := domains.parent_survives input selection
        (domains.regions.origin_survives child)
        ((congrArg CRegion.parent? hkind).trans rfl)
      simp only [hkind, SurvivorDomain.reindexRegion?] at hparent
      rw [domains.regions.index?_index originalParent
        originalParentSurvives] at hparent
      have mappedEq : domains.regions.index originalParent
          originalParentSurvives = parent := Option.some.inj hparent
      have originEq := congrArg domains.regions.origin mappedEq
      have parentEq : originalParent = domains.regions.origin parent :=
        (domains.regions.origin_index originalParent
          originalParentSurvives).symm.trans originEq
      simpa [CRegion.parent?] using congrArg some parentEq
  | bubble originalParent arity =>
      have originalParentSurvives := domains.parent_survives input selection
        (domains.regions.origin_survives child)
        ((congrArg CRegion.parent? hkind).trans rfl)
      simp only [hkind, SurvivorDomain.reindexRegion?] at hparent
      rw [domains.regions.index?_index originalParent
        originalParentSurvives] at hparent
      have mappedEq : domains.regions.index originalParent
          originalParentSurvives = parent := Option.some.inj hparent
      have originEq := congrArg domains.regions.origin mappedEq
      have parentEq : originalParent = domains.regions.origin parent :=
        (domains.regions.origin_index originalParent
          originalParentSurvives).symm.trans originEq
      simpa [CRegion.parent?] using congrArg some parentEq

private theorem removeRaw_climb_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    {steps : Nat} {start finish : domains.regions.Carrier}
    (hclimb : (input.val.removeRaw selection domains).climb steps start =
      some finish) :
    input.val.climb steps (domains.regions.origin start) =
      some (domains.regions.origin finish) := by
  induction steps generalizing start with
  | zero =>
      have equality : start = finish := Option.some.inj hclimb
      subst finish
      rfl
  | succ steps ih =>
      rw [ConcreteDiagram.climb] at hclimb
      cases hparent :
          ((input.val.removeRaw selection domains).regions start).parent? with
      | none =>
          rw [hparent] at hclimb
          contradiction
      | some parent =>
          rw [hparent] at hclimb
          have originalParent := removeRaw_parent_origin input selection domains
            hparent
          rw [ConcreteDiagram.climb, originalParent]
          exact ih hclimb

theorem removeRaw_encloses_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    {ancestor descendant : domains.regions.Carrier}
    (hencloses : (input.val.removeRaw selection domains).Encloses ancestor
      descendant) :
    input.val.Encloses (domains.regions.origin ancestor)
      (domains.regions.origin descendant) := by
  obtain ⟨steps, climb⟩ := hencloses
  have count_le : domains.regions.count ≤ input.val.regionCount := by
    simpa [SurvivorDomain.count, SurvivorDomain.enumeration, filterFin,
      allFin_eq_finRange] using
      List.length_filter_le (domains.regions.survives)
        (allFin input.val.regionCount)
  exact ⟨⟨steps.val, by
    have := steps.isLt
    change steps.val < domains.regions.count + 1 at this
    omega⟩, removeRaw_climb_origin input selection domains climb⟩

private theorem reindexNode_region
    (domain : SurvivorDomain size) (source : CNode size)
    (target : CNode domain.count)
    (ownerSurvives : domain.survives source.region = true)
    (hreindex : domain.reindexNode? source = some target) :
    target.region = domain.index source.region ownerSurvives := by
  cases source with
  | term region ports term =>
      simp only [SurvivorDomain.reindexNode?] at hreindex
      rw [domain.index?_index region ownerSurvives] at hreindex
      cases hreindex
      rfl
  | atom region binder =>
      simp only [SurvivorDomain.reindexNode?] at hreindex
      rw [domain.index?_index region ownerSurvives] at hreindex
      cases hindex : domain.index? binder with
      | none => simp [hindex] at hreindex
      | some mappedBinder =>
          simp [hindex] at hreindex
          cases hreindex
          rfl
  | named region definition arity =>
      simp only [SurvivorDomain.reindexNode?] at hreindex
      rw [domain.index?_index region ownerSurvives] at hreindex
      cases hreindex
      rfl

private theorem deiteration_removeRaw_node_region
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    (node : Fin input.val.nodeCount)
    (survives : domains.nodes.survives node = true) :
    ((input.val.removeRaw selection domains).nodes
        (domains.nodes.index node survives)).region =
      domains.regions.index (input.val.nodes node).region
        (domains.nodeRegion_survives survives) := by
  have reindexed := ConcreteDiagram.removeRaw_node_reindexed input selection
    domains (domains.nodes.index node survives)
  rw [domains.nodes.origin_index node survives] at reindexed
  exact reindexNode_region domains.regions (input.val.nodes node)
    ((input.val.removeRaw selection domains).nodes
      (domains.nodes.index node survives))
    (domains.nodeRegion_survives survives) reindexed

private theorem deiterationRetainedRequest_selectsNode_of_original
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {node : Fin input.val.nodeCount}
    (selected : witness.justifier.val.SelectsNode node) :
    (deiterationRetainedRequest input selection witness).SelectsNode
      ((deiterationDomains input selection).nodes.index node
        (deiterationJustifierNode_survives input selection witness
          ((witness.justifier.mem_selectedNodes node).2 selected))) := by
  rcases selected with direct | regionSelected
  · left
    apply List.mem_filterMap.mpr
    refine ⟨node, direct, ?_⟩
    exact (deiterationDomains input selection).nodes.index?_index node
      (deiterationJustifierNode_survives input selection witness
        ((witness.justifier.mem_selectedNodes node).2 (Or.inl direct)))
  · right
    obtain ⟨root, rootMember, rootEncloses⟩ := regionSelected
    let domains := deiterationDomains input selection
    have rootSelected : root ∈ witness.justifier.selectedRegions :=
      (witness.justifier.mem_selectedRegions root).2
        ⟨root, rootMember, ConcreteDiagram.Encloses.refl input.val root⟩
    have ownerSelected : (input.val.nodes node).region ∈
        witness.justifier.selectedRegions :=
      (witness.justifier.mem_selectedRegions _).2
        ⟨root, rootMember, rootEncloses⟩
    refine ⟨domains.regions.index root
        (deiterationJustifierRegion_survives input selection witness
          rootSelected), ?_, ?_⟩
    · apply List.mem_filterMap.mpr
      exact ⟨root, rootMember, domains.regions.index?_index root
        (deiterationJustifierRegion_survives input selection witness
          rootSelected)⟩
    · rw [deiteration_removeRaw_node_region]
      exact ConcreteDiagram.removeRaw_encloses input selection domains
        (deiterationJustifierRegion_survives input selection witness
          rootSelected)
        (deiterationJustifierRegion_survives input selection witness
          ownerSelected) rootEncloses

theorem deiterationRetainedRequest_valid
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedRequest input selection witness).Valid := by
  let domains := deiterationDomains input selection
  let request := deiterationRetainedRequest input selection witness
  refine {
    childRoots_nodup := ?_
    childRoots_direct := ?_
    directNodes_nodup := ?_
    directNodes_at_anchor := ?_
    explicitWires_nodup := ?_
    explicitWires_at_anchor := ?_
    explicitWireEndpoints_selected := ?_
  }
  · exact filterMap_nodup_of_some_injective
      witness.justifier.property.childRoots_nodup
        (fun {first second mapped} firstEq secondEq => by
          exact (domains.regions.index?_eq_some_iff first mapped).1 firstEq
            |>.symm.trans
              ((domains.regions.index?_eq_some_iff second mapped).1 secondEq))
  · intro mapped member
    have originalMember := deiterationRetainedRequest_childRoot_origin input
      selection witness member
    let original := domains.regions.origin mapped
    have originalSelected : original ∈
        witness.justifier.selectedRegions :=
      (witness.justifier.mem_selectedRegions original).2
        ⟨original, originalMember,
          ConcreteDiagram.Encloses.refl input.val original⟩
    have parent := witness.justifier.property.childRoots_direct original
      originalMember
    have removedParent := ConcreteDiagram.removeRaw_parent input selection
      domains (deiterationJustifierRegion_survives input selection witness
        originalSelected) parent
    have originalIndex : domains.regions.index original
        (deiterationJustifierRegion_survives input selection witness
          originalSelected) = mapped := by
      simpa [original] using domains.regions.index_origin mapped
    rw [originalIndex] at removedParent
    simpa [request, deiterationRetainedRequest, domains] using removedParent
  · exact filterMap_nodup_of_some_injective
      witness.justifier.property.directNodes_nodup
        (fun {first second mapped} firstEq secondEq => by
          exact (domains.nodes.index?_eq_some_iff first mapped).1 firstEq
            |>.symm.trans
              ((domains.nodes.index?_eq_some_iff second mapped).1 secondEq))
  · intro mapped member
    have originalMember := deiterationRetainedRequest_directNode_origin input
      selection witness member
    let original := domains.nodes.origin mapped
    have originalSelected : original ∈ witness.justifier.selectedNodes :=
      (witness.justifier.mem_selectedNodes original).2 (Or.inl originalMember)
    have owner := witness.justifier.property.directNodes_at_anchor original
      originalMember
    have nodeSurvives := deiterationJustifierNode_survives input selection
      witness originalSelected
    have anchorSurvives := deiterationJustifierAnchor_survives input selection
      witness
    have ownerSurvives := domains.nodeRegion_survives nodeSurvives
    have ownerIndexEq : domains.regions.index (input.val.nodes original).region
        ownerSurvives = domains.regions.index witness.justifier.val.anchor
          anchorSurvives := by
      exact survivorIndex_eq_of_eq domains.regions owner ownerSurvives
        anchorSurvives
    have mappedEq : domains.nodes.index original nodeSurvives = mapped := by
      simpa [original] using domains.nodes.index_origin mapped
    rw [← mappedEq]
    cases hnode : input.val.nodes original with
    | term region ports term =>
        rw [ConcreteDiagram.removeRaw_term input selection domains
          nodeSurvives hnode]
        simpa [hnode, request, deiterationRetainedRequest, domains] using
          ownerIndexEq
    | atom region binder =>
        rw [ConcreteDiagram.removeRaw_atom input selection domains
          nodeSurvives hnode]
        simpa [hnode, request, deiterationRetainedRequest, domains] using
          ownerIndexEq
    | named region definition arity =>
        rw [ConcreteDiagram.removeRaw_named input selection domains
          nodeSurvives hnode]
        simpa [hnode, request, deiterationRetainedRequest, domains] using
          ownerIndexEq
  · exact filterMap_nodup_of_some_injective
      witness.justifier.property.explicitWires_nodup
        (fun {first second mapped} firstEq secondEq => by
          exact (domains.wires.index?_eq_some_iff first mapped).1 firstEq
            |>.symm.trans
              ((domains.wires.index?_eq_some_iff second mapped).1 secondEq))
  · intro mapped member
    have originalMember := deiterationRetainedRequest_explicitWire_origin input
      selection witness member
    let original := domains.wires.origin mapped
    have originalSelected : original ∈ witness.justifier.internalWires :=
      witness.justifier.explicitWire_mem_internalWires originalMember
    have scope := witness.justifier.property.explicitWires_at_anchor original
      originalMember
    rw [ConcreteDiagram.removeRaw_wire_scope]
    exact survivorIndex_eq_of_eq domains.regions scope
      (domains.wireScope_survives (by
        simpa [original] using domains.wires.origin_survives mapped))
      (deiterationJustifierAnchor_survives input selection witness)
  · intro mapped member endpoint endpointMember
    have originalMember := deiterationRetainedRequest_explicitWire_origin input
      selection witness member
    let originalWire := domains.wires.origin mapped
    obtain ⟨originalEndpoint, originalEndpointMember, endpointMap⟩ :=
      (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff input selection domains
        mapped endpoint).1 endpointMember
    have originalSelected :=
      witness.justifier.property.explicitWireEndpoints_selected originalWire
        originalMember originalEndpoint originalEndpointMember
    have endpointOrigin := ConcreteDiagram.reindexEndpoint?_origin domains
      endpointMap
    have nodeEq : originalEndpoint.node = domains.nodes.origin endpoint.node := by
      simpa using congrArg CEndpoint.node endpointOrigin
    have mappedNodeEq : domains.nodes.index originalEndpoint.node
        (deiterationJustifierNode_survives input selection witness
          ((witness.justifier.mem_selectedNodes originalEndpoint.node).2
            originalSelected)) = endpoint.node := by
      apply domains.nodes.origin_injective
      rw [domains.nodes.origin_index, nodeEq]
    rw [← mappedNodeEq]
    exact deiterationRetainedRequest_selectsNode_of_original input selection
      witness originalSelected

def deiterationRetainedSelection
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    CheckedSelection
      (input.val.removeRaw selection (deiterationDomains input selection)) :=
  ⟨deiterationRetainedRequest input selection witness,
    deiterationRetainedRequest_valid input selection witness⟩

theorem deiterationRetained_selectsRegion_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : (deiterationDomains input selection).regions.Carrier) :
    (deiterationRetainedRequest input selection witness).SelectsRegion region ↔
      witness.justifier.val.SelectsRegion
        ((deiterationDomains input selection).regions.origin region) := by
  let domains := deiterationDomains input selection
  constructor
  · rintro ⟨root, rootMember, encloses⟩
    exact ⟨domains.regions.origin root,
      deiterationRetainedRequest_childRoot_origin input selection witness
        rootMember,
      removeRaw_encloses_origin input selection domains encloses⟩
  · rintro ⟨root, rootMember, encloses⟩
    have rootSelected : root ∈ witness.justifier.selectedRegions :=
      (witness.justifier.mem_selectedRegions root).2
        ⟨root, rootMember, ConcreteDiagram.Encloses.refl input.val root⟩
    have rootSurvives := deiterationJustifierRegion_survives input selection
      witness rootSelected
    refine ⟨domains.regions.index root rootSurvives, ?_, ?_⟩
    · apply List.mem_filterMap.mpr
      exact ⟨root, rootMember,
        domains.regions.index?_index root rootSurvives⟩
    · have transported := ConcreteDiagram.removeRaw_encloses input selection
        domains rootSurvives (domains.regions.origin_survives region) encloses
      have indexEq := domains.regions.index_origin region
      rw [indexEq] at transported
      exact transported

private theorem deiteration_removeRaw_node_region_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    (node : domains.nodes.Carrier) :
    domains.regions.origin
        ((input.val.removeRaw selection domains).nodes node).region =
      (input.val.nodes (domains.nodes.origin node)).region := by
  have mapped := deiteration_removeRaw_node_region input selection domains
    (domains.nodes.origin node) (domains.nodes.origin_survives node)
  rw [domains.nodes.index_origin] at mapped
  rw [mapped, domains.regions.origin_index]

theorem deiterationRetained_selectsNode_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : (deiterationDomains input selection).nodes.Carrier) :
    (deiterationRetainedRequest input selection witness).SelectsNode node ↔
      witness.justifier.val.SelectsNode
        ((deiterationDomains input selection).nodes.origin node) := by
  let domains := deiterationDomains input selection
  constructor
  · rintro (direct | selectedOwner)
    · exact Or.inl
        (deiterationRetainedRequest_directNode_origin input selection witness
          direct)
    · right
      have selectedOriginal :=
        (deiterationRetained_selectsRegion_iff input selection witness
          ((input.val.removeRaw selection domains).nodes node).region).1
          selectedOwner
      rw [deiteration_removeRaw_node_region_origin input selection domains
        node] at selectedOriginal
      exact selectedOriginal
  · rintro (direct | selectedOwner)
    · left
      apply List.mem_filterMap.mpr
      exact ⟨domains.nodes.origin node, direct, domains.nodes.index?_origin node⟩
    · right
      apply (deiterationRetained_selectsRegion_iff input selection witness
        ((input.val.removeRaw selection domains).nodes node).region).2
      rw [deiteration_removeRaw_node_region_origin input selection domains node]
      exact selectedOwner

private theorem deiteration_removeRaw_wire_scope_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    (wire : domains.wires.Carrier) :
    domains.regions.origin
        ((input.val.removeRaw selection domains).wires wire).scope =
      (input.val.wires (domains.wires.origin wire)).scope := by
  rw [ConcreteDiagram.removeRaw_wire_scope,
    domains.regions.origin_index]

theorem deiterationRetained_selectsWire_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : (deiterationDomains input selection).wires.Carrier) :
    (deiterationRetainedRequest input selection witness).SelectsWire wire ↔
      witness.justifier.val.SelectsWire
        ((deiterationDomains input selection).wires.origin wire) := by
  let domains := deiterationDomains input selection
  constructor
  · rintro (selectedScope | explicit)
    · left
      have selectedOriginal :=
        (deiterationRetained_selectsRegion_iff input selection witness
          ((input.val.removeRaw selection domains).wires wire).scope).1
          selectedScope
      rw [deiteration_removeRaw_wire_scope_origin input selection domains
        wire] at selectedOriginal
      exact selectedOriginal
    · exact Or.inr
        (deiterationRetainedRequest_explicitWire_origin input selection witness
          explicit)
  · rintro (selectedScope | explicit)
    · left
      apply (deiterationRetained_selectsRegion_iff input selection witness
        ((input.val.removeRaw selection domains).wires wire).scope).2
      rw [deiteration_removeRaw_wire_scope_origin input selection domains wire]
      exact selectedScope
    · right
      apply List.mem_filterMap.mpr
      exact ⟨domains.wires.origin wire, explicit,
        domains.wires.index?_origin wire⟩

private theorem filterFin_survivor_origin
    (domain : SurvivorDomain size)
    (sourceP : Fin size → Bool)
    (targetP : domain.Carrier → Bool)
    (predicateEq : ∀ index, targetP index = sourceP (domain.origin index))
    (subset : ∀ original, sourceP original = true →
      domain.survives original = true) :
    (filterFin targetP).map domain.origin = filterFin sourceP := by
  have enumerationEq :
      (allFin domain.count).map domain.origin = domain.enumeration := by
    rw [allFin_eq_finRange, List.finRange, List.map_ofFn]
    change List.ofFn (fun index => domain.enumeration.get index) =
      domain.enumeration
    exact List.ofFn_getElem
  unfold filterFin
  have filterEq :
      List.filter targetP (allFin domain.count) =
        List.filter (sourceP ∘ domain.origin) (allFin domain.count) := by
    apply congrArg (fun predicate => List.filter predicate (allFin domain.count))
    funext index
    exact predicateEq index
  rw [filterEq, ← List.filter_map, enumerationEq]
  change List.filter sourceP
      (List.filter domain.survives (allFin size)) =
    List.filter sourceP (allFin size)
  rw [List.filter_filter]
  apply congrArg (fun predicate => List.filter predicate (allFin size))
  funext original
  cases selected : sourceP original with
  | false => simp [selected]
  | true => simp [selected, subset original selected]

theorem deiterationRetained_selectedRegions_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).selectedRegions.map
        (deiterationDomains input selection).regions.origin =
      witness.justifier.selectedRegions := by
  apply filterFin_survivor_origin
  · intro region
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact deiterationRetained_selectsRegion_iff input selection witness region
  · intro original selected
    apply deiterationJustifierRegion_survives input selection witness
    apply (witness.justifier.mem_selectedRegions original).2
    exact of_decide_eq_true selected

theorem deiterationRetained_selectedNodes_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).selectedNodes.map
        (deiterationDomains input selection).nodes.origin =
      witness.justifier.selectedNodes := by
  apply filterFin_survivor_origin
  · intro node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact deiterationRetained_selectsNode_iff input selection witness node
  · intro original selected
    apply deiterationJustifierNode_survives input selection witness
    apply (witness.justifier.mem_selectedNodes original).2
    exact of_decide_eq_true selected

theorem deiterationRetained_internalWires_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).internalWires.map
        (deiterationDomains input selection).wires.origin =
      witness.justifier.internalWires := by
  apply filterFin_survivor_origin
  · intro wire
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact deiterationRetained_selectsWire_iff input selection witness wire
  · intro original selected
    apply deiterationJustifierWire_survives input selection witness
    apply (witness.justifier.mem_internalWires original).2
    exact of_decide_eq_true selected

theorem deiterationRetained_touchesWire_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : (deiterationDomains input selection).wires.Carrier) :
    (¬ (deiterationRetainedRequest input selection witness).SelectsWire wire ∧
        ∃ endpoint,
          endpoint ∈ ((input.val.removeRaw selection
            (deiterationDomains input selection)).wires wire).endpoints ∧
          (deiterationRetainedRequest input selection witness).SelectsNode
            endpoint.node) ↔
      (¬ witness.justifier.val.SelectsWire
          ((deiterationDomains input selection).wires.origin wire) ∧
        ∃ endpoint,
          endpoint ∈ (input.val.wires
            ((deiterationDomains input selection).wires.origin wire)).endpoints ∧
          witness.justifier.val.SelectsNode endpoint.node) := by
  let domains := deiterationDomains input selection
  constructor
  · rintro ⟨notInternal, endpoint, endpointMember, selectedNode⟩
    refine ⟨fun selectedOriginal => notInternal
      ((deiterationRetained_selectsWire_iff input selection witness wire).2
        selectedOriginal), ?_⟩
    obtain ⟨original, originalMember, endpointMap⟩ :=
      (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff input selection domains
        wire endpoint).1 endpointMember
    refine ⟨original, originalMember, ?_⟩
    have selectedOriginal :=
      (deiterationRetained_selectsNode_iff input selection witness
        endpoint.node).1 selectedNode
    have endpointOrigin := ConcreteDiagram.reindexEndpoint?_origin domains
      endpointMap
    have nodeEq : original.node = domains.nodes.origin endpoint.node := by
      simpa using congrArg CEndpoint.node endpointOrigin
    rw [nodeEq]
    exact selectedOriginal
  · rintro ⟨notInternal, original, originalMember, selectedNode⟩
    refine ⟨fun selectedMapped => notInternal
      ((deiterationRetained_selectsWire_iff input selection witness wire).1
        selectedMapped), ?_⟩
    have selectedNodeMember : original.node ∈
        witness.justifier.selectedNodes :=
      (witness.justifier.mem_selectedNodes original.node).2 selectedNode
    have nodeSurvives := deiterationJustifierNode_survives input selection
      witness selectedNodeMember
    have wireSurvives := domains.incidentWire_survives input selection
      originalMember nodeSurvives
    have wireEq : domains.wires.index (domains.wires.origin wire)
        wireSurvives = wire := domains.wires.index_origin wire
    let mappedEndpoint : CEndpoint domains.nodes.count := {
      node := domains.nodes.index original.node nodeSurvives
      port := original.port
    }
    refine ⟨mappedEndpoint, ?_, ?_⟩
    · apply (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff input selection
        domains wire mappedEndpoint).2
      refine ⟨original, originalMember, ?_⟩
      unfold SurvivorDomain.reindexEndpoint?
      rw [domains.nodes.index?_index original.node nodeSurvives]
      rfl
    · apply (deiterationRetained_selectsNode_iff input selection witness
        mappedEndpoint.node).2
      have originEq :
          (deiterationDomains input selection).nodes.origin
              mappedEndpoint.node = original.node := by
        dsimp [mappedEndpoint]
        exact domains.nodes.origin_index original.node nodeSurvives
      rw [originEq]
      exact selectedNode

theorem deiterationRetained_touchingWires_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).touchingWires.map
        (deiterationDomains input selection).wires.origin =
      witness.justifier.touchingWires := by
  apply filterFin_survivor_origin
  · intro wire
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact deiterationRetained_touchesWire_iff input selection witness wire
  · intro original selected
    have justifierMember : original ∈ witness.justifier.touchingWires :=
      (witness.justifier.mem_touchingWires original).2
        (of_decide_eq_true selected)
    have selectedMember : original ∈ selection.touchingWires := by
      rw [← witness.sameAttachments]
      exact justifierMember
    apply ((deiterationDomains input selection).wire_survives_iff original).2
    exact (selection.mem_touchingWires_consequences selectedMember).1

theorem deiterationRetained_usesExternalBinder_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (binder : (deiterationDomains input selection).regions.Carrier) :
    (deiterationRetainedSelection input selection witness).UsesExternalBinder
        binder ↔
      witness.justifier.UsesExternalBinder
        ((deiterationDomains input selection).regions.origin binder) := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  constructor
  · rintro ⟨binderNotSelected, node, selectedNode, atom⟩
    refine ⟨?_, domains.nodes.origin node, ?_, ?_⟩
    · intro selectedOriginal
      exact binderNotSelected
        ((deiterationRetainedSelection input selection witness
          |>.mem_selectedRegions binder).2
          ((deiterationRetained_selectsRegion_iff input selection witness
            binder).2
            ((witness.justifier.mem_selectedRegions
              (domains.regions.origin binder)).1 selectedOriginal)))
    · apply (witness.justifier.mem_selectedNodes
        (domains.nodes.origin node)).2
      exact (deiterationRetained_selectsNode_iff input selection witness
        node).1 ((retained.mem_selectedNodes node).1 selectedNode)
    · have originalSurvives := domains.nodes.origin_survives node
      have nodeIndex := domains.nodes.index_origin node
      cases hnode : input.val.nodes (domains.nodes.origin node) with
      | term region freePorts term =>
          rw [← nodeIndex, ConcreteDiagram.removeRaw_term input selection
            domains originalSurvives hnode] at atom
          simpa [hnode] using atom
      | named region definition arity =>
          rw [← nodeIndex, ConcreteDiagram.removeRaw_named input selection
            domains originalSurvives hnode] at atom
          simpa [hnode] using atom
      | atom region originalBinder =>
          rw [← nodeIndex, ConcreteDiagram.removeRaw_atom input selection
            domains originalSurvives hnode] at atom
          simp only [hnode]
          have binderEq : domains.regions.index originalBinder
              (domains.atomBinder_survives input selection originalSurvives
                hnode) = binder := atom
          exact (domains.regions.origin_index originalBinder _).symm.trans
            (congrArg domains.regions.origin binderEq)
  · rintro ⟨binderNotSelected, originalNode, selectedNode, atom⟩
    have selectedNodeProp :=
      (witness.justifier.mem_selectedNodes originalNode).1 selectedNode
    have nodeSurvives := deiterationJustifierNode_survives input selection
      witness selectedNode
    let mappedNode := domains.nodes.index originalNode nodeSurvives
    refine ⟨?_, mappedNode, ?_, ?_⟩
    · intro selectedMapped
      exact binderNotSelected
        ((witness.justifier.mem_selectedRegions
          (domains.regions.origin binder)).2
          ((deiterationRetained_selectsRegion_iff input selection witness
            binder).1 ((retained.mem_selectedRegions binder).1
              selectedMapped)))
    · apply (retained.mem_selectedNodes mappedNode).2
      exact deiterationRetainedRequest_selectsNode_of_original input selection
        witness selectedNodeProp
    · cases hnode : input.val.nodes originalNode with
      | term region freePorts term => simpa [hnode] using atom
      | named region definition arity => simpa [hnode] using atom
      | atom region originalBinder =>
          simp only [hnode] at atom
          subst originalBinder
          rw [ConcreteDiagram.removeRaw_atom input selection domains
            nodeSurvives hnode]
          simp only
          have binderIndex := domains.regions.index_origin binder
          exact binderIndex

private theorem checked_climb_steps_le_regionCount
    (checked : CheckedDiagram signature)
    {steps : Nat} {start finish : Fin checked.val.regionCount}
    (climb : checked.val.climb steps start = some finish) :
    steps ≤ checked.val.regionCount := by
  obtain ⟨tail, tailClimb⟩ := checked.property.all_regions_reach_root finish
  have rootClimb := ConcreteElaboration.climb_add climb tailClimb
  have totalBound :=
    ConcreteElaboration.ParentTraversal.checked_climb_to_root_steps_le_regionCount
      checked rootClimb
  omega

private theorem removeRaw_climb_option_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    (start : Fin input.val.regionCount)
    (startSurvives : domains.regions.survives start = true)
    (steps : Nat) :
    Option.map domains.regions.origin
        ((input.val.removeRaw selection domains).climb steps
          (domains.regions.index start startSurvives)) =
      input.val.climb steps start := by
  cases sourceClimb : input.val.climb steps start with
  | some finish =>
      obtain ⟨finishSurvives, removedClimb⟩ :=
        ConcreteDiagram.removeRaw_climb input selection domains startSurvives
          sourceClimb
      rw [removedClimb]
      exact congrArg some
        (domains.regions.origin_index finish finishSurvives)
  | none =>
      cases removedClimb : (input.val.removeRaw selection domains).climb steps
          (domains.regions.index start startSurvives) with
      | none => rfl
      | some finish =>
          have originalClimb := removeRaw_climb_origin input selection domains
            removedClimb
          rw [domains.regions.origin_index] at originalClimb
          rw [sourceClimb] at originalClimb
          contradiction

private theorem filterMap_allFin_add_of_none
    (small extra : Nat) (f : Nat → Option α)
    (noneAfter : ∀ steps, small ≤ steps → f steps = none) :
    (allFin (small + extra)).filterMap (fun index => f index.val) =
      (allFin small).filterMap (fun index => f index.val) := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [show small + (extra + 1) = (small + extra) + 1 by omega,
        allFin_eq_finRange, List.finRange_succ_last,
        List.filterMap_append, List.filterMap_map]
      simp only [Function.comp_apply, Fin.val_castSucc, Fin.val_last,
        List.filterMap]
      rw [noneAfter (small + extra) (by omega)]
      simp only [List.filterMap_nil, List.append_nil]
      rw [← allFin_eq_finRange]
      exact ih

theorem deiterationRetained_anchorChain_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness
      |>.anchorChainInnerFirst).map
        (deiterationDomains input selection).regions.origin =
      witness.justifier.anchorChainInnerFirst := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  have anchorSurvives := deiterationJustifierAnchor_survives input selection
    witness
  have mappedAnchor : domains.regions.index witness.justifier.val.anchor
      anchorSurvives = retained.val.anchor := rfl
  have functionEq :
      (fun steps : Fin (domains.regions.count + 1) =>
        Option.map domains.regions.origin
          ((input.val.removeRaw selection domains).climb steps.val
            retained.val.anchor)) =
      (fun steps : Fin (domains.regions.count + 1) =>
        input.val.climb steps.val witness.justifier.val.anchor) := by
    funext steps
    rw [← mappedAnchor]
    exact removeRaw_climb_option_origin input selection domains
      witness.justifier.val.anchor anchorSurvives steps.val
  unfold CheckedSelection.anchorChainInnerFirst
  change List.map domains.regions.origin
      (List.filterMap
        (fun steps : Fin (domains.regions.count + 1) =>
          (input.val.removeRaw selection domains).climb steps.val
            retained.val.anchor)
        (allFin (domains.regions.count + 1))) =
    List.filterMap
      (fun steps : Fin (input.val.regionCount + 1) =>
        input.val.climb steps.val witness.justifier.val.anchor)
      (allFin (input.val.regionCount + 1))
  rw [List.map_filterMap, functionEq]
  have count_le : domains.regions.count ≤ input.val.regionCount := by
    simpa [SurvivorDomain.count, SurvivorDomain.enumeration, filterFin,
      allFin_eq_finRange] using
      List.length_filter_le (domains.regions.survives)
        (allFin input.val.regionCount)
  have noneAfter : ∀ steps, domains.regions.count + 1 ≤ steps →
      input.val.climb steps witness.justifier.val.anchor = none := by
    intro steps beyond
    cases sourceClimb : input.val.climb steps witness.justifier.val.anchor with
    | none => rfl
    | some finish =>
        obtain ⟨finishSurvives, removedClimb⟩ :=
          ConcreteDiagram.removeRaw_climb input selection domains
            anchorSurvives sourceClimb
        let removed : CheckedDiagram signature :=
          ⟨input.val.removeRaw selection domains,
            ConcreteDiagram.removeRaw_wellFormed input selection domains⟩
        have stepsBound := checked_climb_steps_le_regionCount removed
          removedClimb
        change steps ≤ domains.regions.count at stepsBound
        omega
  have truncated := filterMap_allFin_add_of_none
    (domains.regions.count + 1)
    (input.val.regionCount - domains.regions.count)
    (fun steps => input.val.climb steps witness.justifier.val.anchor)
    noneAfter
  have sizeEq : domains.regions.count + 1 +
      (input.val.regionCount - domains.regions.count) =
      input.val.regionCount + 1 := by omega
  rw [sizeEq] at truncated
  exact truncated.symm

private theorem eraseDups_map_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (injective : Function.Injective f) :
    ∀ values : List α,
      (values.map f).eraseDups = values.eraseDups.map f
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.map_cons]
      congr 1
      rw [← eraseDups_map_injective f injective
        (tail.filter fun value => !value == head)]
      apply congrArg List.eraseDups
      rw [List.filter_map]
      apply congrArg (List.map f)
      apply congrArg (fun predicate => List.filter predicate tail)
      funext value
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp [injective.eq_iff]
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

theorem deiterationRetained_externalBinders_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).externalBinders.map
        (deiterationDomains input selection).regions.origin =
      witness.justifier.externalBinders := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  let targetValues := retained.anchorChainInnerFirst.reverse
  let sourceValues := witness.justifier.anchorChainInnerFirst.reverse
  have chainEq : targetValues.map domains.regions.origin = sourceValues := by
    have base := deiterationRetained_anchorChain_origin input selection witness
    dsimp only [targetValues, sourceValues]
    calc
      retained.anchorChainInnerFirst.reverse.map domains.regions.origin =
          (retained.anchorChainInnerFirst.map
            domains.regions.origin).reverse := by
            exact List.map_reverse
              (f := domains.regions.origin)
              (l := retained.anchorChainInnerFirst)
      _ = witness.justifier.anchorChainInnerFirst.reverse :=
        congrArg List.reverse base
      _ = sourceValues := rfl
  have predicateEq :
      (fun binder : domains.regions.Carrier =>
        decide (retained.UsesExternalBinder binder)) =
      (fun binder =>
        decide (witness.justifier.UsesExternalBinder
          (domains.regions.origin binder))) := by
    funext binder
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact deiterationRetained_usesExternalBinder_iff input selection witness
      binder
  have filteredEq :
      (targetValues.filter fun binder =>
        decide (retained.UsesExternalBinder binder)).map
          domains.regions.origin =
      sourceValues.filter fun binder =>
        decide (witness.justifier.UsesExternalBinder binder) := by
    let sourceP := fun binder =>
      decide (witness.justifier.UsesExternalBinder binder)
    have targetFilterEq :
        targetValues.filter (fun binder =>
          decide (retained.UsesExternalBinder binder)) =
        targetValues.filter (sourceP ∘ domains.regions.origin) := by
      apply congrArg (fun predicate => targetValues.filter predicate)
      exact predicateEq
    calc
      (targetValues.filter fun binder =>
          decide (retained.UsesExternalBinder binder)).map
            domains.regions.origin =
          (targetValues.filter
            (sourceP ∘ domains.regions.origin)).map
              domains.regions.origin := congrArg
                (List.map domains.regions.origin) targetFilterEq
      _ = (targetValues.map domains.regions.origin).filter sourceP := by
        exact List.filter_map.symm
      _ = sourceValues.filter sourceP := congrArg
        (List.filter sourceP) chainEq
  unfold CheckedSelection.externalBinders
  change ((targetValues.filter fun binder =>
      decide (retained.UsesExternalBinder binder)).eraseDups).map
      domains.regions.origin =
    (sourceValues.filter fun binder =>
      decide (witness.justifier.UsesExternalBinder binder)).eraseDups
  calc
    ((targetValues.filter fun binder =>
        decide (retained.UsesExternalBinder binder)).eraseDups).map
        domains.regions.origin =
      ((targetValues.filter fun binder =>
        decide (retained.UsesExternalBinder binder)).map
          domains.regions.origin).eraseDups :=
        (eraseDups_map_injective domains.regions.origin
          domains.regions.origin_injective _).symm
    _ = (sourceValues.filter fun binder =>
        decide (witness.justifier.UsesExternalBinder binder)).eraseDups :=
      congrArg List.eraseDups filteredEq

end VisualProof.Rule.IterationSoundness
