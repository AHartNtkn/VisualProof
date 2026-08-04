import VisualProof.Diagram.Concrete.Subgraph.Selection
import VisualProof.Diagram.Concrete.Subgraph.Reindex
import VisualProof.Diagram.Concrete.WellFormed
import VisualProof.Diagram.Concrete.Elaboration.Context

namespace VisualProof.Diagram

open VisualProof.Data.Finite

private theorem climb_prefix_exists {d : ConcreteDiagram}
    {start finish : Fin d.regionCount} {first second : Nat}
    (hle : first ≤ second)
    (hfinish : d.climb second start = some finish) :
    ∃ middle, d.climb first start = some middle := by
  induction first generalizing start second with
  | zero => exact ⟨start, rfl⟩
  | succ first ih =>
      cases second with
      | zero => omega
      | succ second =>
          cases hparent : (d.regions start).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at hfinish
          | some parent =>
              have htail : d.climb second parent = some finish := by
                simpa [ConcreteDiagram.climb, hparent] using hfinish
              obtain ⟨middle, hmiddle⟩ :=
                ih (Nat.le_of_succ_le_succ hle) htail
              exact ⟨middle, by
                simpa [ConcreteDiagram.climb, hparent] using hmiddle⟩

private theorem climb_cancel_prefix {d : ConcreteDiagram}
    {start middle finish : Fin d.regionCount} {first second : Nat}
    (hle : first ≤ second)
    (hfirst : d.climb first start = some middle)
    (hsecond : d.climb second start = some finish) :
    d.climb (second - first) middle = some finish := by
  induction first generalizing start second with
  | zero =>
      have heq : start = middle := Option.some.inj hfirst
      subst middle
      simpa using hsecond
  | succ first ih =>
      cases second with
      | zero => omega
      | succ second =>
          cases hparent : (d.regions start).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at hfirst
          | some parent =>
              have hfirstTail : d.climb first parent = some middle := by
                simpa [ConcreteDiagram.climb, hparent] using hfirst
              have hsecondTail : d.climb second parent = some finish := by
                simpa [ConcreteDiagram.climb, hparent] using hsecond
              simpa using ih (Nat.le_of_succ_le_succ hle)
                hfirstTail hsecondTail

namespace SelectionRequest.SelectsRegion

/-- Selecting an ancestor selects every region below it. -/
theorem downward {d : ConcreteDiagram} (hwf : d.WellFormed signature)
    {request : SelectionRequest d} {ancestor descendant : Fin d.regionCount}
    (hselected : request.SelectsRegion ancestor)
    (hencloses : d.Encloses ancestor descendant) :
    request.SelectsRegion descendant := by
  obtain ⟨root, hroot, hrootAncestor⟩ := hselected
  exact ⟨root, hroot,
    ConcreteElaboration.checked_encloses_trans hwf hrootAncestor hencloses⟩

end SelectionRequest.SelectsRegion

/-- Dense survivor receipts shared by frame construction and decomposition. -/
structure FrameDomains (d : ConcreteDiagram) (selection : CheckedSelection d) where
  regions : SurvivorDomain d.regionCount :=
    ⟨fun region => decide (region = d.root ∨ region ∉ selection.selectedRegions)⟩
  regions_exact : ∀ region, regions.survives region =
      decide (region = d.root ∨ region ∉ selection.selectedRegions) := by
    intro region
    rfl
  nodes : SurvivorDomain d.nodeCount :=
    ⟨fun node => decide (node ∉ selection.selectedNodes)⟩
  nodes_exact : ∀ node, nodes.survives node =
      decide (node ∉ selection.selectedNodes) := by
    intro node
    rfl
  wires : SurvivorDomain d.wireCount :=
    ⟨fun wire => decide (wire ∉ selection.internalWires)⟩
  wires_exact : ∀ wire, wires.survives wire =
      decide (wire ∉ selection.internalWires) := by
    intro wire
    rfl

namespace FrameDomains

private theorem parent_encloses (d : ConcreteDiagram)
    {child parent : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent) :
    d.Encloses parent child := by
  have hpositive := child.isLt
  refine ⟨⟨1, by omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, hparent]

@[simp] theorem region_survives_iff (domains : FrameDomains d selection)
    (region : Fin d.regionCount) :
    domains.regions.survives region = true ↔
      region = d.root ∨ region ∉ selection.selectedRegions := by
  rw [domains.regions_exact]
  simp

@[simp] theorem node_survives_iff (domains : FrameDomains d selection)
    (node : Fin d.nodeCount) :
    domains.nodes.survives node = true ↔
      node ∉ selection.selectedNodes := by
  rw [domains.nodes_exact]
  simp

@[simp] theorem wire_survives_iff (domains : FrameDomains d selection)
    (wire : Fin d.wireCount) :
    domains.wires.survives wire = true ↔
      wire ∉ selection.internalWires := by
  rw [domains.wires_exact]
  simp

@[simp] theorem root_survives (domains : FrameDomains d selection) :
    domains.regions.survives d.root = true := by
  rw [domains.regions_exact]
  simp

/-- The compact identifier of the retained sheet root. -/
def root (domains : FrameDomains d selection) : domains.regions.Carrier :=
  domains.regions.index d.root domains.root_survives

@[simp] theorem root_origin (domains : FrameDomains d selection) :
    domains.regions.origin domains.root = d.root := by
  exact domains.regions.origin_index d.root domains.root_survives

/-- Every parent of a surviving region also survives. -/
theorem parent_survives (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {region parent : Fin host.val.regionCount}
    (hregion : domains.regions.survives region = true)
    (hparent : (host.val.regions region).parent? = some parent) :
    domains.regions.survives parent = true := by
  apply (domains.region_survives_iff parent).2
  by_cases hroot : parent = host.val.root
  · exact Or.inl hroot
  · right
    intro hselectedParent
    have hselectedRegion : region ∈ selection.selectedRegions :=
      (selection.mem_selectedRegions region).2
        ((selection.mem_selectedRegions parent).1 hselectedParent |>.downward
          host.property (parent_encloses host.val hparent))
    rcases (domains.region_survives_iff region).1 hregion with
      hregionRoot | hnotSelected
    · subst region
      have hsheet := host.property.root_is_sheet
      unfold ConcreteDiagram.RootIsSheet at hsheet
      rw [hsheet] at hparent
      contradiction
    · exact hnotSelected hselectedRegion

/-- The owner of every surviving node survives. -/
theorem nodeRegion_survives (domains : FrameDomains d selection)
    {node : Fin d.nodeCount} (hnode : domains.nodes.survives node = true) :
    domains.regions.survives (d.nodes node).region = true := by
  apply (domains.region_survives_iff (d.nodes node).region).2
  by_cases hroot : (d.nodes node).region = d.root
  · exact Or.inl hroot
  · right
    intro hselectedRegion
    have hselectedNode : node ∈ selection.selectedNodes :=
      (selection.mem_selectedNodes node).2
        (Or.inr ((selection.mem_selectedRegions _).1 hselectedRegion))
    exact ((domains.node_survives_iff node).1 hnode) hselectedNode

/-- The binder of every surviving atom survives. -/
theorem atomBinder_survives (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {node : Fin host.val.nodeCount} {region binder : Fin host.val.regionCount}
    (hnodeSurvives : domains.nodes.survives node = true)
    (hnode : host.val.nodes node = .atom region binder) :
    domains.regions.survives binder = true := by
  apply (domains.region_survives_iff binder).2
  by_cases hroot : binder = host.val.root
  · exact Or.inl hroot
  · right
    intro hselectedBinder
    have hbinderEncloses := host.property.atom_binders_enclose node
    simp only [hnode] at hbinderEncloses
    have hselectedRegion : selection.val.SelectsRegion region :=
      ((selection.mem_selectedRegions binder).1 hselectedBinder).downward
        host.property hbinderEncloses
    have hselectedNode : node ∈ selection.selectedNodes :=
      (selection.mem_selectedNodes node).2 (by
        right
        simpa only [hnode, CNode.region] using hselectedRegion)
    exact ((domains.node_survives_iff node).1 hnodeSurvives) hselectedNode

/-- The scope of every surviving wire survives. -/
theorem wireScope_survives (domains : FrameDomains d selection)
    {wire : Fin d.wireCount} (hwire : domains.wires.survives wire = true) :
    domains.regions.survives (d.wires wire).scope = true := by
  apply (domains.region_survives_iff (d.wires wire).scope).2
  by_cases hroot : (d.wires wire).scope = d.root
  · exact Or.inl hroot
  · right
    intro hselectedScope
    have hinternal : wire ∈ selection.internalWires :=
      selection.selectedScope_mem_internalWires
        ((selection.mem_selectedRegions _).1 hselectedScope)
    exact ((domains.wire_survives_iff wire).1 hwire) hinternal

/-- Any wire incident to a surviving node also survives. -/
theorem incidentWire_survives (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {wire : Fin host.val.wireCount} {endpoint : CEndpoint host.val.nodeCount}
    (hendpoint : endpoint ∈ (host.val.wires wire).endpoints)
    (hnode : domains.nodes.survives endpoint.node = true) :
    domains.wires.survives wire = true := by
  apply (domains.wire_survives_iff wire).2
  intro hinternal
  rcases (selection.mem_internalWires_expanded wire).1 hinternal with
    hscope | hexplicit
  · have hencloses := host.property.wire_scopes_enclose wire endpoint hendpoint
    have hselectedRegion : selection.val.SelectsRegion
        (host.val.nodes endpoint.node).region :=
      hscope.downward host.property hencloses
    have hselectedNode : endpoint.node ∈ selection.selectedNodes :=
      (selection.mem_selectedNodes endpoint.node).2 (Or.inr hselectedRegion)
    exact ((domains.node_survives_iff endpoint.node).1 hnode) hselectedNode
  · have hselectedNode := selection.explicitWire_endpoint_selected
      hexplicit hendpoint
    exact ((domains.node_survives_iff endpoint.node).1 hnode) hselectedNode

end FrameDomains

namespace ConcreteDiagram

private def fallbackNode (domains : FrameDomains d selection) :
    CNode domains.regions.count :=
  .term domains.root 0 (.lam (.bvar 0))

private def frameRegion (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection)
    (region : domains.regions.Carrier) : CRegion domains.regions.count :=
  (domains.regions.reindexRegion?
    (d.regions (domains.regions.origin region))).getD .sheet

private def frameNode (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection)
    (node : domains.nodes.Carrier) : CNode domains.regions.count :=
  (domains.regions.reindexNode?
    (d.nodes (domains.nodes.origin node))).getD (fallbackNode domains)

private def frameEndpoints (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection)
    (wire : domains.wires.Carrier) : List (CEndpoint domains.nodes.count) :=
  (d.wires (domains.wires.origin wire)).endpoints.filterMap
    domains.nodes.reindexEndpoint?

private def frameWire (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection)
    (wire : domains.wires.Carrier) :
    CWire domains.regions.count domains.nodes.count :=
  let original := d.wires (domains.wires.origin wire)
  {
    scope := (domains.regions.index? original.scope).getD domains.root
    endpoints := d.frameEndpoints selection domains wire
  }

/--
The deterministic raw frame. Selected regions and nodes and internal wires are
removed; surviving wire endpoints are restricted to surviving nodes. Dense
identifiers are exactly the accompanying survivor receipts.
-/
def removeRaw (d : ConcreteDiagram) (selection : CheckedSelection d)
    (domains : FrameDomains d selection := {}) : ConcreteDiagram where
  regionCount := domains.regions.count
  nodeCount := domains.nodes.count
  wireCount := domains.wires.count
  root := domains.root
  regions := d.frameRegion selection domains
  nodes := d.frameNode selection domains
  wires := d.frameWire selection domains

/-- The region fallback is unreachable for every checked survivor. -/
theorem removeRaw_region_reindexed
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : domains.regions.Carrier) :
    domains.regions.reindexRegion?
        (host.val.regions (domains.regions.origin region)) =
      some ((host.val.removeRaw selection domains).regions region) := by
  change domains.regions.reindexRegion?
      (host.val.regions (domains.regions.origin region)) =
    some (host.val.frameRegion selection domains region)
  unfold frameRegion
  cases hregion : host.val.regions (domains.regions.origin region) with
  | sheet =>
      rfl
  | cut parent =>
      have hparent :
          (host.val.regions (domains.regions.origin region)).parent? =
            some parent := (congrArg CRegion.parent? hregion).trans rfl
      have hsurvives := domains.parent_survives host selection
        (domains.regions.origin_survives region) hparent
      simp only [SurvivorDomain.reindexRegion?]
      rw [domains.regions.index?_index parent hsurvives]
      rfl
  | bubble parent arity =>
      have hparent :
          (host.val.regions (domains.regions.origin region)).parent? =
            some parent := (congrArg CRegion.parent? hregion).trans rfl
      have hsurvives := domains.parent_survives host selection
        (domains.regions.origin_survives region) hparent
      simp only [SurvivorDomain.reindexRegion?]
      rw [domains.regions.index?_index parent hsurvives]
      rfl

/-- The node fallback is unreachable for every checked survivor. -/
theorem removeRaw_node_reindexed
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (node : domains.nodes.Carrier) :
    domains.regions.reindexNode?
        (host.val.nodes (domains.nodes.origin node)) =
      some ((host.val.removeRaw selection domains).nodes node) := by
  change domains.regions.reindexNode?
      (host.val.nodes (domains.nodes.origin node)) =
    some (host.val.frameNode selection domains node)
  unfold frameNode
  cases hnode : host.val.nodes (domains.nodes.origin node) with
  | term region freePorts term =>
      have hregion := domains.nodeRegion_survives
        (domains.nodes.origin_survives node)
      simp only [hnode, CNode.region] at hregion
      simp only [SurvivorDomain.reindexNode?]
      rw [domains.regions.index?_index region hregion]
      rfl
  | atom region binder =>
      have hregion := domains.nodeRegion_survives
        (domains.nodes.origin_survives node)
      simp only [hnode, CNode.region] at hregion
      have hbinder := domains.atomBinder_survives host selection
        (domains.nodes.origin_survives node) hnode
      simp only [SurvivorDomain.reindexNode?]
      rw [domains.regions.index?_index region hregion,
        domains.regions.index?_index binder hbinder]
      rfl
  | named region definition arity =>
      have hregion := domains.nodeRegion_survives
        (domains.nodes.origin_survives node)
      simp only [hnode, CNode.region] at hregion
      simp only [SurvivorDomain.reindexNode?]
      rw [domains.regions.index?_index region hregion]
      rfl

/-- Surviving wire scopes are reindexed exactly, never replaced by the root. -/
theorem removeRaw_wire_scope
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (wire : domains.wires.Carrier) :
    ((host.val.removeRaw selection domains).wires wire).scope =
      domains.regions.index
        (host.val.wires (domains.wires.origin wire)).scope
        (domains.wireScope_survives (domains.wires.origin_survives wire)) := by
  change ((host.val.frameWire selection domains wire).scope) = _
  unfold frameWire
  dsimp only
  have hscope := domains.wireScope_survives
    (domains.wires.origin_survives wire)
  rw [domains.regions.index?_index _ hscope]
  rfl

/-- Parent links commute with dense survivor reindexing. -/
theorem removeRaw_parent
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {region parent : Fin host.val.regionCount}
    (hregion : domains.regions.survives region = true)
    (hparent : (host.val.regions region).parent? = some parent) :
    ((host.val.removeRaw selection domains).regions
      (domains.regions.index region hregion)).parent? =
        some (domains.regions.index parent
          (domains.parent_survives host selection hregion hparent)) := by
  change ((domains.regions.reindexRegion?
    (host.val.regions (domains.regions.origin
      (domains.regions.index region hregion)))).getD .sheet).parent? = _
  rw [domains.regions.origin_index region hregion]
  cases hkind : host.val.regions region with
  | sheet =>
      rw [hkind] at hparent
      contradiction
  | cut originalParent =>
      rw [hkind] at hparent
      have heq : originalParent = parent := by
        exact Option.some.inj hparent
      subst originalParent
      simp only [SurvivorDomain.reindexRegion?]
      rw [domains.regions.index?_index]
      rfl
  | bubble originalParent arity =>
      rw [hkind] at hparent
      have heq : originalParent = parent := by
        exact Option.some.inj hparent
      subst originalParent
      simp only [SurvivorDomain.reindexRegion?]
      rw [domains.regions.index?_index]
      rfl

/-- The retained sheet remains the unique root sheet. -/
theorem removeRaw_root_is_sheet
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).RootIsSheet := by
  unfold RootIsSheet
  have hreindexed := ConcreteDiagram.removeRaw_region_reindexed host selection domains
    domains.root
  rw [domains.root_origin, host.property.root_is_sheet] at hreindexed
  exact (Option.some.inj hreindexed).symm

theorem removeRaw_only_root_is_sheet
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).OnlyRootIsSheet := by
  intro region hsheet
  change host.val.frameRegion selection domains region = .sheet at hsheet
  unfold frameRegion at hsheet
  cases hkind : host.val.regions (domains.regions.origin region) with
  | sheet =>
      have horiginRoot := host.property.only_root_is_sheet
        (domains.regions.origin region) hkind
      change region = domains.root
      apply domains.regions.origin_injective
      rw [horiginRoot, domains.root_origin]
  | cut parent =>
      have hparent :
          (host.val.regions (domains.regions.origin region)).parent? =
            some parent := (congrArg CRegion.parent? hkind).trans rfl
      have hsurvives := domains.parent_survives host selection
        (domains.regions.origin_survives region) hparent
      rw [hkind] at hsheet
      simp only [SurvivorDomain.reindexRegion?] at hsheet
      rw [domains.regions.index?_index parent hsurvives] at hsheet
      contradiction
  | bubble parent arity =>
      have hparent :
          (host.val.regions (domains.regions.origin region)).parent? =
            some parent := (congrArg CRegion.parent? hkind).trans rfl
      have hsurvives := domains.parent_survives host selection
        (domains.regions.origin_survives region) hparent
      rw [hkind] at hsheet
      simp only [SurvivorDomain.reindexRegion?] at hsheet
      rw [domains.regions.index?_index parent hsurvives] at hsheet
      contradiction

/-- Finite parent traversal commutes with survivor compaction. -/
theorem removeRaw_climb
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {steps : Nat} {start finish : Fin host.val.regionCount}
    (hstart : domains.regions.survives start = true)
    (hclimb : host.val.climb steps start = some finish) :
    ∃ hfinish : domains.regions.survives finish = true,
      (host.val.removeRaw selection domains).climb steps
          (domains.regions.index start hstart) =
        some (domains.regions.index finish hfinish) := by
  induction steps generalizing start with
  | zero =>
      have heq : start = finish := Option.some.inj hclimb
      subst finish
      exact ⟨hstart, rfl⟩
  | succ steps ih =>
      cases hparent : (host.val.regions start).parent? with
      | none => simp [ConcreteDiagram.climb, hparent] at hclimb
      | some parent =>
          have hparentSurvives := domains.parent_survives host selection
            hstart hparent
          have htail : host.val.climb steps parent = some finish := by
            simpa [ConcreteDiagram.climb, hparent] using hclimb
          obtain ⟨hfinish, hframeTail⟩ := ih hparentSurvives htail
          refine ⟨hfinish, ?_⟩
          simp only [ConcreteDiagram.climb]
          rw [ConcreteDiagram.removeRaw_parent host selection domains hstart hparent]
          exact hframeTail

/-- A retained root path has at most as many edges as retained regions. -/
theorem removeRaw_climb_to_root_steps_lt_regionCount
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {steps : Nat} {start : Fin host.val.regionCount}
    (hstart : domains.regions.survives start = true)
    (hroot : host.val.climb steps start = some host.val.root) :
    steps < domains.regions.count := by
  classical
  let pathIsSome (index : Fin (steps + 1)) :
      (host.val.climb index.val start).isSome = true :=
    Option.isSome_iff_exists.mpr
      (climb_prefix_exists (Nat.le_of_lt_succ index.isLt) hroot)
  let path (index : Fin (steps + 1)) : Fin host.val.regionCount :=
    (host.val.climb index.val start).get (pathIsSome index)
  have path_spec (index : Fin (steps + 1)) :
      host.val.climb index.val start = some (path index) := by
    exact (Option.some_get (pathIsSome index)).symm
  let pathSurvives (index : Fin (steps + 1)) :
      domains.regions.survives (path index) = true :=
    Exists.choose (ConcreteDiagram.removeRaw_climb host selection domains
      hstart (path_spec index))
  let embed (index : Fin (steps + 1)) : domains.regions.Carrier :=
    domains.regions.index (path index) (pathSurvives index)
  have embed_injective : Function.Injective embed := by
    intro first second heq
    have hpaths : path first = path second := by
      have horigins := congrArg domains.regions.origin heq
      calc
        path first = domains.regions.origin (embed first) := by
          symm
          exact domains.regions.origin_index (path first) (pathSurvives first)
        _ = domains.regions.origin (embed second) := horigins
        _ = path second :=
          domains.regions.origin_index (path second) (pathSurvives second)
    have hfirstSuffix := climb_cancel_prefix
      (Nat.le_of_lt_succ first.isLt) (path_spec first) hroot
    have hsecondSuffix := climb_cancel_prefix
      (Nat.le_of_lt_succ second.isLt) (path_spec second) hroot
    rw [hpaths] at hfirstSuffix
    have hremaining :=
      ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique host.val
        host.property.root_is_sheet hfirstSuffix hsecondSuffix
    apply Fin.ext
    omega
  have hcard := fin_card_le_of_injective embed embed_injective
  omega

theorem removeRaw_all_regions_reach_root
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).AllRegionsReachRoot := by
  intro region
  obtain ⟨steps, hhostClimb⟩ :=
    host.property.all_regions_reach_root (domains.regions.origin region)
  have hbound :=
    ConcreteDiagram.removeRaw_climb_to_root_steps_lt_regionCount
      host selection domains (domains.regions.origin_survives region) hhostClimb
  obtain ⟨hroot, hframeClimb⟩ :=
    ConcreteDiagram.removeRaw_climb host selection domains
      (domains.regions.origin_survives region) hhostClimb
  refine ⟨⟨steps.val, by
    change steps.val < domains.regions.count + 1
    omega⟩, ?_⟩
  rw [domains.regions.index_origin] at hframeClimb
  change (host.val.removeRaw selection domains).climb steps.val region =
    some domains.root
  simpa [FrameDomains.root] using hframeClimb

/-- Enclosure is preserved exactly between surviving regions. -/
theorem removeRaw_encloses
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {ancestor descendant : Fin host.val.regionCount}
    (hancestor : domains.regions.survives ancestor = true)
    (hdescendant : domains.regions.survives descendant = true)
    (hencloses : host.val.Encloses ancestor descendant) :
    (host.val.removeRaw selection domains).Encloses
      (domains.regions.index ancestor hancestor)
      (domains.regions.index descendant hdescendant) := by
  obtain ⟨steps, hclimb⟩ := hencloses
  obtain ⟨rootSteps, hancestorRoot⟩ :=
    host.property.all_regions_reach_root ancestor
  have hdescendantRoot :
      host.val.climb (steps.val + rootSteps.val) descendant =
        some host.val.root :=
    ConcreteElaboration.climb_add hclimb hancestorRoot
  have hbound :=
    ConcreteDiagram.removeRaw_climb_to_root_steps_lt_regionCount
      host selection domains hdescendant hdescendantRoot
  obtain ⟨hfinish, hframeClimb⟩ :=
    ConcreteDiagram.removeRaw_climb host selection domains hdescendant hclimb
  refine ⟨⟨steps.val, by
    change steps.val < domains.regions.count + 1
    omega⟩, ?_⟩
  simpa using hframeClimb

theorem removeRaw_bubble
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {region parent : Fin host.val.regionCount} {arity : Nat}
    (hregion : domains.regions.survives region = true)
    (hkind : host.val.regions region = .bubble parent arity) :
    (host.val.removeRaw selection domains).regions
        (domains.regions.index region hregion) =
      .bubble
        (domains.regions.index parent
          (domains.parent_survives host selection hregion
            ((congrArg CRegion.parent? hkind).trans rfl))) arity := by
  change (domains.regions.reindexRegion?
    (host.val.regions (domains.regions.origin
      (domains.regions.index region hregion)))).getD .sheet = _
  rw [domains.regions.origin_index region hregion]
  simp only [hkind, SurvivorDomain.reindexRegion?]
  rw [domains.regions.index?_index]
  rfl

theorem removeRaw_term
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {node : Fin host.val.nodeCount} {region : Fin host.val.regionCount}
    {freePorts : Nat} {term : Lambda.Term 0 (Fin freePorts)}
    (hnodeSurvives : domains.nodes.survives node = true)
    (hnode : host.val.nodes node = .term region freePorts term) :
    (host.val.removeRaw selection domains).nodes
        (domains.nodes.index node hnodeSurvives) =
      .term
        (domains.regions.index region (by
          simpa only [hnode, CNode.region] using
            domains.nodeRegion_survives hnodeSurvives))
        freePorts term := by
  change (domains.regions.reindexNode?
    (host.val.nodes (domains.nodes.origin
      (domains.nodes.index node hnodeSurvives)))).getD
        (fallbackNode domains) = _
  rw [domains.nodes.origin_index node hnodeSurvives]
  simp only [hnode, SurvivorDomain.reindexNode?]
  rw [domains.regions.index?_index]
  rfl

theorem removeRaw_atom
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {node : Fin host.val.nodeCount} {region binder : Fin host.val.regionCount}
    (hnodeSurvives : domains.nodes.survives node = true)
    (hnode : host.val.nodes node = .atom region binder) :
    (host.val.removeRaw selection domains).nodes
        (domains.nodes.index node hnodeSurvives) =
      .atom
        (domains.regions.index region (by
          simpa only [hnode, CNode.region] using
            domains.nodeRegion_survives hnodeSurvives))
        (domains.regions.index binder
          (domains.atomBinder_survives host selection hnodeSurvives hnode)) := by
  change (domains.regions.reindexNode?
    (host.val.nodes (domains.nodes.origin
      (domains.nodes.index node hnodeSurvives)))).getD
        (fallbackNode domains) = _
  rw [domains.nodes.origin_index node hnodeSurvives]
  simp only [hnode, SurvivorDomain.reindexNode?]
  rw [domains.regions.index?_index, domains.regions.index?_index]
  rfl

theorem removeRaw_named
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {node : Fin host.val.nodeCount} {region : Fin host.val.regionCount}
    {definition arity : Nat}
    (hnodeSurvives : domains.nodes.survives node = true)
    (hnode : host.val.nodes node = .named region definition arity) :
    (host.val.removeRaw selection domains).nodes
        (domains.nodes.index node hnodeSurvives) =
      .named
        (domains.regions.index region (by
          simpa only [hnode, CNode.region] using
            domains.nodeRegion_survives hnodeSurvives))
        definition arity := by
  change (domains.regions.reindexNode?
    (host.val.nodes (domains.nodes.origin
      (domains.nodes.index node hnodeSurvives)))).getD
        (fallbackNode domains) = _
  rw [domains.nodes.origin_index node hnodeSurvives]
  simp only [hnode, SurvivorDomain.reindexNode?]
  rw [domains.regions.index?_index]
  rfl

theorem removeRaw_atom_binders_are_bubbles
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).AtomBindersAreBubbles := by
  intro node
  let original := domains.nodes.origin node
  have hsurvives := domains.nodes.origin_survives node
  have hindex : domains.nodes.index original hsurvives = node :=
    domains.nodes.index_origin node
  cases hnode : host.val.nodes original with
  | term region freePorts term =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_term host selection domains hsurvives hnode]
      trivial
  | named region definition arity =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_named host selection domains hsurvives hnode]
      trivial
  | atom region binder =>
      have hbubble := host.property.atom_binders_are_bubbles original
      simp only [hnode] at hbubble
      obtain ⟨parent, arity, hkind⟩ := hbubble
      have hbinderSurvives :=
        domains.atomBinder_survives host selection hsurvives hnode
      rw [← hindex,
        ConcreteDiagram.removeRaw_atom host selection domains hsurvives hnode]
      simp only
      rw [ConcreteDiagram.removeRaw_bubble host selection domains
        hbinderSurvives hkind]
      exact ⟨_, _, rfl⟩

theorem removeRaw_named_references_resolve
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).NamedReferencesResolve signature := by
  intro node
  let original := domains.nodes.origin node
  have hsurvives := domains.nodes.origin_survives node
  have hindex : domains.nodes.index original hsurvives = node :=
    domains.nodes.index_origin node
  cases hnode : host.val.nodes original with
  | term region freePorts term =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_term host selection domains hsurvives hnode]
      trivial
  | atom region binder =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_atom host selection domains hsurvives hnode]
      trivial
  | named region definition arity =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_named host selection domains hsurvives hnode]
      have hresolve := host.property.named_references_resolve original
      simpa only [hnode] using hresolve

theorem removeRaw_atom_binders_enclose
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).AtomBindersEnclose := by
  intro node
  let original := domains.nodes.origin node
  have hsurvives := domains.nodes.origin_survives node
  have hindex : domains.nodes.index original hsurvives = node :=
    domains.nodes.index_origin node
  cases hnode : host.val.nodes original with
  | term region freePorts term =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_term host selection domains hsurvives hnode]
      trivial
  | named region definition arity =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_named host selection domains hsurvives hnode]
      trivial
  | atom region binder =>
      have hregion : domains.regions.survives region = true := by
        have howner := domains.nodeRegion_survives hsurvives
        rw [hnode] at howner
        exact howner
      have hbinder :=
        domains.atomBinder_survives host selection hsurvives hnode
      have hencloses := host.property.atom_binders_enclose original
      simp only [hnode] at hencloses
      rw [← hindex,
        ConcreteDiagram.removeRaw_atom host selection domains hsurvives hnode]
      exact ConcreteDiagram.removeRaw_encloses host selection domains
        hbinder hregion hencloses

theorem removeRaw_requiresPort_iff
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (node : domains.nodes.Carrier) (port : CPort) :
    (host.val.removeRaw selection domains).RequiresPort node port ↔
      host.val.RequiresPort (domains.nodes.origin node) port := by
  let original := domains.nodes.origin node
  have hsurvives := domains.nodes.origin_survives node
  have hindex : domains.nodes.index original hsurvives = node :=
    domains.nodes.index_origin node
  cases hnode : host.val.nodes original with
  | term region freePorts term =>
      rw [← hindex]
      rw [domains.nodes.origin_index original hsurvives]
      unfold ConcreteDiagram.RequiresPort
      rw [ConcreteDiagram.removeRaw_term host selection domains hsurvives hnode]
      simp only [hnode]
  | named region definition arity =>
      rw [← hindex]
      rw [domains.nodes.origin_index original hsurvives]
      unfold ConcreteDiagram.RequiresPort
      rw [ConcreteDiagram.removeRaw_named host selection domains hsurvives hnode]
      simp only [hnode]
  | atom region binder =>
      have hbubble := host.property.atom_binders_are_bubbles original
      simp only [hnode] at hbubble
      obtain ⟨parent, arity, hkind⟩ := hbubble
      have hbinderSurvives :=
        domains.atomBinder_survives host selection hsurvives hnode
      rw [← hindex]
      rw [domains.nodes.origin_index original hsurvives]
      unfold ConcreteDiagram.RequiresPort
      rw [ConcreteDiagram.removeRaw_atom host selection domains hsurvives hnode]
      simp only [hnode]
      rw [ConcreteDiagram.removeRaw_bubble host selection domains
        hbinderSurvives hkind]
      simp only
      simp only [hkind]

@[simp] theorem removeRaw_wire_endpoints
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (wire : domains.wires.Carrier) :
    ((host.val.removeRaw selection domains).wires wire).endpoints =
      (host.val.wires (domains.wires.origin wire)).endpoints.filterMap
        domains.nodes.reindexEndpoint? := rfl

theorem mem_removeRaw_wire_endpoints_iff
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (wire : domains.wires.Carrier)
    (endpoint : CEndpoint domains.nodes.count) :
    endpoint ∈ ((host.val.removeRaw selection domains).wires wire).endpoints ↔
      ∃ original,
        original ∈ (host.val.wires (domains.wires.origin wire)).endpoints ∧
          domains.nodes.reindexEndpoint? original = some endpoint := by
  rw [ConcreteDiagram.removeRaw_wire_endpoints host selection domains]
  exact List.mem_filterMap

theorem reindexEndpoint?_origin
    (domains : FrameDomains d selection)
    {original : CEndpoint d.nodeCount}
    {mapped : CEndpoint domains.nodes.count}
    (hreindex : domains.nodes.reindexEndpoint? original = some mapped) :
    original = { node := domains.nodes.origin mapped.node, port := mapped.port } := by
  obtain ⟨node, hnode, heq⟩ :=
    (domains.nodes.reindexEndpoint?_eq_some_iff original mapped).1 hreindex
  have horigin := (domains.nodes.index?_eq_some_iff original.node node).1 hnode
  subst mapped
  simp only at horigin
  cases original
  cases horigin
  rfl

theorem reindexEndpoint?_some_injective
    (domains : FrameDomains d selection)
    {first second : CEndpoint d.nodeCount}
    {mapped : CEndpoint domains.nodes.count}
    (hfirst : domains.nodes.reindexEndpoint? first = some mapped)
    (hsecond : domains.nodes.reindexEndpoint? second = some mapped) :
    first = second := by
  rw [ConcreteDiagram.reindexEndpoint?_origin domains hfirst,
    ConcreteDiagram.reindexEndpoint?_origin domains hsecond]

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
      | none =>
          simpa [List.filterMap, hmapped] using ih htail
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

theorem removeRaw_endpoints_are_nodup
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).EndpointsAreNodup := by
  intro wire
  rw [ConcreteDiagram.removeRaw_wire_endpoints host selection domains]
  exact filterMap_nodup_of_some_injective
    (host.property.endpoints_are_nodup (domains.wires.origin wire))
    (fun hfirst hsecond =>
      ConcreteDiagram.reindexEndpoint?_some_injective domains hfirst hsecond)

theorem removeRaw_wire_endpoints_are_disjoint
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).WireEndpointsAreDisjoint := by
  intro first second hne endpoint hfirst
  rw [Bool.not_eq_true', decide_eq_false_iff_not]
  intro hsecond
  obtain ⟨firstOriginal, hfirstMember, hfirstMapped⟩ :=
    (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff host selection domains
      first endpoint).1 hfirst
  obtain ⟨secondOriginal, hsecondMember, hsecondMapped⟩ :=
    (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff host selection domains
      second endpoint).1 hsecond
  have hsame := ConcreteDiagram.reindexEndpoint?_some_injective domains
    hfirstMapped hsecondMapped
  subst secondOriginal
  have hneProp : first ≠ second := by simpa using hne
  have hwireNe : domains.wires.origin first ≠ domains.wires.origin second := by
    intro heq
    exact hneProp (domains.wires.origin_injective heq)
  have hwireNeBool :
      (domains.wires.origin first != domains.wires.origin second) = true := by
    simpa using hwireNe
  have hdisjoint := host.property.wire_endpoints_are_disjoint
    (domains.wires.origin first) (domains.wires.origin second) hwireNeBool
    firstOriginal hfirstMember
  rw [Bool.not_eq_true', decide_eq_false_iff_not] at hdisjoint
  exact hdisjoint hsecondMember

theorem removeRaw_endpointOccurs_of_surviving
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {wire : Fin host.val.wireCount} {endpoint : CEndpoint host.val.nodeCount}
    (hendpoint : host.val.EndpointOccurs wire endpoint)
    (hnode : domains.nodes.survives endpoint.node = true) :
    ∃ mappedWire,
      (host.val.removeRaw selection domains).EndpointOccurs mappedWire
        { node := domains.nodes.index endpoint.node hnode, port := endpoint.port } := by
  have hwire := domains.incidentWire_survives host selection
    hendpoint hnode
  let mappedWire := domains.wires.index wire hwire
  refine ⟨mappedWire, ?_⟩
  apply (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff host selection domains
    mappedWire _).2
  refine ⟨endpoint, ?_, ?_⟩
  · change endpoint ∈ (host.val.wires (domains.wires.origin mappedWire)).endpoints
    rw [show domains.wires.origin mappedWire = wire by
      exact domains.wires.origin_index wire hwire]
    exact hendpoint
  · unfold SurvivorDomain.reindexEndpoint?
    rw [domains.nodes.index?_index endpoint.node hnode]
    rfl

theorem removeRaw_required_ports_are_covered
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).RequiredPortsAreCovered := by
  intro node
  let original := domains.nodes.origin node
  have hsurvives := domains.nodes.origin_survives node
  have hindex : domains.nodes.index original hsurvives = node :=
    domains.nodes.index_origin node
  cases hnode : host.val.nodes original with
  | term region freePorts term =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_term host selection domains hsurvives hnode]
      simp only
      have hcovered := host.property.required_ports_are_covered original
      simp only [hnode] at hcovered
      constructor
      · obtain ⟨wire, hwire⟩ := hcovered.1
        exact ConcreteDiagram.removeRaw_endpointOccurs_of_surviving
          host selection domains hwire hsurvives
      · intro port
        obtain ⟨wire, hwire⟩ := hcovered.2 port
        exact ConcreteDiagram.removeRaw_endpointOccurs_of_surviving
          host selection domains hwire hsurvives
  | named region definition arity =>
      rw [← hindex,
        ConcreteDiagram.removeRaw_named host selection domains hsurvives hnode]
      simp only
      have hcovered := host.property.required_ports_are_covered original
      simp only [hnode] at hcovered
      intro port
      obtain ⟨wire, hwire⟩ := hcovered port
      exact ConcreteDiagram.removeRaw_endpointOccurs_of_surviving
        host selection domains hwire hsurvives
  | atom region binder =>
      have hbubble := host.property.atom_binders_are_bubbles original
      simp only [hnode] at hbubble
      obtain ⟨parent, arity, hkind⟩ := hbubble
      have hbinderSurvives :=
        domains.atomBinder_survives host selection hsurvives hnode
      rw [← hindex,
        ConcreteDiagram.removeRaw_atom host selection domains hsurvives hnode]
      simp only
      rw [ConcreteDiagram.removeRaw_bubble host selection domains
        hbinderSurvives hkind]
      simp only
      have hcovered := host.property.required_ports_are_covered original
      simp only [hnode, hkind] at hcovered
      intro port
      obtain ⟨wire, hwire⟩ := hcovered port
      exact ConcreteDiagram.removeRaw_endpointOccurs_of_surviving
        host selection domains hwire hsurvives

theorem removeRaw_endpoints_are_valid
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).EndpointsAreValid := by
  intro wire endpoint hendpoint
  obtain ⟨original, horiginal, hreindex⟩ :=
    (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff host selection domains
      wire endpoint).1 hendpoint
  have hvalid := host.property.endpoints_are_valid
    (domains.wires.origin wire) original horiginal
  have horigin := ConcreteDiagram.reindexEndpoint?_origin domains hreindex
  rw [horigin] at hvalid
  exact (ConcreteDiagram.removeRaw_requiresPort_iff host selection domains
    endpoint.node endpoint.port).2 hvalid

theorem removeRaw_wire_scopes_enclose
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).WireScopesEnclose := by
  intro wire endpoint hendpoint
  obtain ⟨originalEndpoint, horiginalMember, hreindex⟩ :=
    (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff host selection domains
      wire endpoint).1 hendpoint
  have horiginal := ConcreteDiagram.reindexEndpoint?_origin domains hreindex
  rw [horiginal] at horiginalMember
  let originalNode := domains.nodes.origin endpoint.node
  have hnodeSurvives := domains.nodes.origin_survives endpoint.node
  have hnodeIndex : domains.nodes.index originalNode hnodeSurvives = endpoint.node :=
    domains.nodes.index_origin endpoint.node
  have hscopeSurvives := domains.wireScope_survives
    (domains.wires.origin_survives wire)
  have hhostEncloses := host.property.wire_scopes_enclose
    (domains.wires.origin wire)
    ({ node := originalNode, port := endpoint.port } :
      CEndpoint host.val.nodeCount) horiginalMember
  rw [ConcreteDiagram.removeRaw_wire_scope host selection domains wire]
  cases hnode : host.val.nodes originalNode with
  | term region freePorts term =>
      have hregion : domains.regions.survives region = true := by
        have howner := domains.nodeRegion_survives hnodeSurvives
        rw [hnode] at howner
        exact howner
      have hencloses : host.val.Encloses
          (host.val.wires (domains.wires.origin wire)).scope region := by
        simpa only [hnode, CNode.region] using hhostEncloses
      rw [← hnodeIndex,
        ConcreteDiagram.removeRaw_term host selection domains hnodeSurvives hnode]
      exact ConcreteDiagram.removeRaw_encloses host selection domains
        hscopeSurvives hregion hencloses
  | atom region binder =>
      have hregion : domains.regions.survives region = true := by
        have howner := domains.nodeRegion_survives hnodeSurvives
        rw [hnode] at howner
        exact howner
      have hencloses : host.val.Encloses
          (host.val.wires (domains.wires.origin wire)).scope region := by
        simpa only [hnode, CNode.region] using hhostEncloses
      rw [← hnodeIndex,
        ConcreteDiagram.removeRaw_atom host selection domains hnodeSurvives hnode]
      exact ConcreteDiagram.removeRaw_encloses host selection domains
        hscopeSurvives hregion hencloses
  | named region definition arity =>
      have hregion : domains.regions.survives region = true := by
        have howner := domains.nodeRegion_survives hnodeSurvives
        rw [hnode] at howner
        exact howner
      have hencloses : host.val.Encloses
          (host.val.wires (domains.wires.origin wire)).scope region := by
        simpa only [hnode, CNode.region] using hhostEncloses
      rw [← hnodeIndex,
        ConcreteDiagram.removeRaw_named host selection domains hnodeSurvives hnode]
      exact ConcreteDiagram.removeRaw_encloses host selection domains
        hscopeSurvives hregion hencloses

/-- Removal preserves every concrete well-formedness clause. -/
theorem removeRaw_wellFormed
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    (host.val.removeRaw selection domains).WellFormed signature where
  root_is_sheet := ConcreteDiagram.removeRaw_root_is_sheet host selection domains
  only_root_is_sheet :=
    ConcreteDiagram.removeRaw_only_root_is_sheet host selection domains
  all_regions_reach_root :=
    ConcreteDiagram.removeRaw_all_regions_reach_root host selection domains
  atom_binders_are_bubbles :=
    ConcreteDiagram.removeRaw_atom_binders_are_bubbles host selection domains
  atom_binders_enclose :=
    ConcreteDiagram.removeRaw_atom_binders_enclose host selection domains
  named_references_resolve :=
    ConcreteDiagram.removeRaw_named_references_resolve host selection domains
  endpoints_are_valid :=
    ConcreteDiagram.removeRaw_endpoints_are_valid host selection domains
  endpoints_are_nodup :=
    ConcreteDiagram.removeRaw_endpoints_are_nodup host selection domains
  wire_endpoints_are_disjoint :=
    ConcreteDiagram.removeRaw_wire_endpoints_are_disjoint host selection domains
  required_ports_are_covered :=
    ConcreteDiagram.removeRaw_required_ports_are_covered host selection domains
  wire_scopes_enclose :=
    ConcreteDiagram.removeRaw_wire_scopes_enclose host selection domains

@[simp] theorem removeRaw_regionCount (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection) :
    (d.removeRaw selection domains).regionCount = domains.regions.count := rfl

@[simp] theorem removeRaw_nodeCount (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection) :
    (d.removeRaw selection domains).nodeCount = domains.nodes.count := rfl

@[simp] theorem removeRaw_wireCount (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection) :
    (d.removeRaw selection domains).wireCount = domains.wires.count := rfl

@[simp] theorem removeRaw_root (d : ConcreteDiagram)
    (selection : CheckedSelection d) (domains : FrameDomains d selection) :
    (d.removeRaw selection domains).root = domains.root := rfl

/-- Run the sole concrete well-formedness authority on the computed frame. -/
def removeChecked (signature : List Nat) (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection := {}) :
    Except WFError (CheckedDiagram signature) :=
  checkWellFormed signature (host.val.removeRaw selection domains)

theorem removeChecked_sound
    (h : removeChecked signature host selection domains = .ok frame) :
    frame.val = host.val.removeRaw selection domains ∧
      frame.val.WellFormed signature := by
  constructor
  · exact checkWellFormed_preserves_input h
  · exact frame.property

theorem removeChecked_complete :
    removeChecked signature host selection domains =
      .ok ⟨host.val.removeRaw selection domains,
        removeRaw_wellFormed host selection domains⟩ := by
  exact checkWellFormed_complete (removeRaw_wellFormed host selection domains)

end ConcreteDiagram

end VisualProof.Diagram
