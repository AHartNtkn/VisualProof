import VisualProof.Diagram.Concrete.Examples
import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

namespace CRegion

def rename (regions : FiniteEquiv (Fin sourceRegions) (Fin targetRegions)) :
    CRegion sourceRegions -> CRegion targetRegions
  | .sheet => .sheet
  | .cut parent => .cut (regions parent)
  | .bubble parent arity => .bubble (regions parent) arity

@[simp] theorem parent?_rename
    (regions : FiniteEquiv (Fin sourceRegions) (Fin targetRegions))
    (region : CRegion sourceRegions) :
    (region.rename regions).parent? = region.parent?.map regions := by
  cases region <;> rfl

@[simp] theorem rename_refl (region : CRegion regions) :
    region.rename (.refl (Fin regions)) = region := by
  cases region <;> rfl

@[simp] theorem rename_symm_rename
    (regions : FiniteEquiv (Fin sourceRegions) (Fin targetRegions))
    (region : CRegion sourceRegions) :
    (region.rename regions).rename regions.symm = region := by
  cases region <;> simp [rename]

@[simp] theorem rename_trans
    (first : FiniteEquiv (Fin firstRegions) (Fin secondRegions))
    (second : FiniteEquiv (Fin secondRegions) (Fin thirdRegions))
    (region : CRegion firstRegions) :
    (region.rename first).rename second = region.rename (first.trans second) := by
  cases region <;> rfl

end CRegion

namespace CNode

def rename (regions : FiniteEquiv (Fin sourceRegions) (Fin targetRegions)) :
    CNode sourceRegions -> CNode targetRegions
  | .term region freePorts body => CNode.term (regions region) freePorts body
  | .atom region binder => CNode.atom (regions region) (regions binder)
  | .named region definition arity =>
      CNode.named (regions region) definition arity

@[simp] theorem region_rename
    (regions : FiniteEquiv (Fin sourceRegions) (Fin targetRegions))
    (node : CNode sourceRegions) :
    (node.rename regions).region = regions node.region := by
  cases node <;> simp [rename, CNode.region]

@[simp] theorem rename_refl (node : CNode regions) :
    node.rename (.refl (Fin regions)) = node := by
  cases node <;> rfl

@[simp] theorem rename_symm_rename
    (regions : FiniteEquiv (Fin sourceRegions) (Fin targetRegions))
    (node : CNode sourceRegions) :
    (node.rename regions).rename regions.symm = node := by
  cases node <;> simp [rename]

@[simp] theorem rename_trans
    (first : FiniteEquiv (Fin firstRegions) (Fin secondRegions))
    (second : FiniteEquiv (Fin secondRegions) (Fin thirdRegions))
    (node : CNode firstRegions) :
    (node.rename first).rename second = node.rename (first.trans second) := by
  cases node <;> rfl

end CNode

namespace CEndpoint

def rename (nodes : FiniteEquiv (Fin sourceNodes) (Fin targetNodes))
    (endpoint : CEndpoint sourceNodes) : CEndpoint targetNodes :=
  { node := nodes endpoint.node, port := endpoint.port }

@[simp] theorem rename_node
    (nodes : FiniteEquiv (Fin sourceNodes) (Fin targetNodes))
    (endpoint : CEndpoint sourceNodes) :
    (endpoint.rename nodes).node = nodes endpoint.node := rfl

@[simp] theorem rename_port
    (nodes : FiniteEquiv (Fin sourceNodes) (Fin targetNodes))
    (endpoint : CEndpoint sourceNodes) :
    (endpoint.rename nodes).port = endpoint.port := rfl

@[simp] theorem rename_refl (endpoint : CEndpoint nodes) :
    endpoint.rename (.refl (Fin nodes)) = endpoint := by
  cases endpoint
  rfl

@[simp] theorem rename_symm_rename
    (nodes : FiniteEquiv (Fin sourceNodes) (Fin targetNodes))
    (endpoint : CEndpoint sourceNodes) :
    (endpoint.rename nodes).rename nodes.symm = endpoint := by
  cases endpoint
  simp [rename]

@[simp] theorem rename_rename_symm
    (nodes : FiniteEquiv (Fin sourceNodes) (Fin targetNodes))
    (endpoint : CEndpoint targetNodes) :
    (endpoint.rename nodes.symm).rename nodes = endpoint := by
  cases endpoint with
  | mk node port =>
      unfold rename
      congr
      exact nodes.right_inv node

@[simp] theorem rename_trans
    (first : FiniteEquiv (Fin firstNodes) (Fin secondNodes))
    (second : FiniteEquiv (Fin secondNodes) (Fin thirdNodes))
    (endpoint : CEndpoint firstNodes) :
    (endpoint.rename first).rename second = endpoint.rename (first.trans second) := by
  rfl

theorem rename_injective
    (nodes : FiniteEquiv (Fin sourceNodes) (Fin targetNodes)) :
    Function.Injective (rename nodes) := by
  intro left right h
  have := congrArg (rename nodes.symm) h
  simpa only [rename_symm_rename] using this

end CEndpoint

structure ConcreteIso (source target : ConcreteDiagram) where
  regionCount_eq : source.regionCount = target.regionCount
  nodeCount_eq : source.nodeCount = target.nodeCount
  wireCount_eq : source.wireCount = target.wireCount
  regions : FiniteEquiv (Fin source.regionCount) (Fin target.regionCount)
  nodes : FiniteEquiv (Fin source.nodeCount) (Fin target.nodeCount)
  wires : FiniteEquiv (Fin source.wireCount) (Fin target.wireCount)
  root_eq : regions source.root = target.root
  regions_eq : forall region,
    (source.regions region).rename regions = target.regions (regions region)
  nodes_eq : forall node,
    (source.nodes node).rename regions = target.nodes (nodes node)
  wire_scope_eq : forall wire,
    regions (source.wires wire).scope = (target.wires (wires wire)).scope
  wire_endpoints_perm : forall wire,
    ((source.wires wire).endpoints.map (CEndpoint.rename nodes)).Perm
      (target.wires (wires wire)).endpoints

namespace ConcreteIso

def refl (diagram : ConcreteDiagram) : ConcreteIso diagram diagram where
  regionCount_eq := rfl
  nodeCount_eq := rfl
  wireCount_eq := rfl
  regions := .refl _
  nodes := .refl _
  wires := .refl _
  root_eq := rfl
  regions_eq := by simp
  nodes_eq := by simp
  wire_scope_eq := by simp
  wire_endpoints_perm := by
    intro wire
    change ((diagram.wires wire).endpoints.map
      (CEndpoint.rename (.refl _))).Perm (diagram.wires wire).endpoints
    induction (diagram.wires wire).endpoints with
    | nil => exact .nil
    | cons head tail ih =>
        simpa only [List.map_cons, CEndpoint.rename_refl] using ih.cons head

def symm {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) : ConcreteIso target source where
  regionCount_eq := iso.regionCount_eq.symm
  nodeCount_eq := iso.nodeCount_eq.symm
  wireCount_eq := iso.wireCount_eq.symm
  regions := iso.regions.symm
  nodes := iso.nodes.symm
  wires := iso.wires.symm
  root_eq := by
    rw [<- iso.root_eq]
    exact iso.regions.left_inv source.root
  regions_eq := by
    intro region
    calc
      (target.regions region).rename iso.regions.symm =
          (target.regions (iso.regions (iso.regions.symm region))).rename
            iso.regions.symm := congrArg
              (fun r => (target.regions r).rename iso.regions.symm)
              (iso.regions.right_inv region).symm
      _ = ((source.regions (iso.regions.symm region)).rename iso.regions).rename
            iso.regions.symm := by rw [iso.regions_eq]
      _ = source.regions (iso.regions.symm region) := by
            simp only [CRegion.rename_symm_rename]
  nodes_eq := by
    intro node
    calc
      (target.nodes node).rename iso.regions.symm =
          (target.nodes (iso.nodes (iso.nodes.symm node))).rename
            iso.regions.symm := congrArg
              (fun n => (target.nodes n).rename iso.regions.symm)
              (iso.nodes.right_inv node).symm
      _ = ((source.nodes (iso.nodes.symm node)).rename iso.regions).rename
            iso.regions.symm := by rw [iso.nodes_eq]
      _ = source.nodes (iso.nodes.symm node) := by
            simp only [CNode.rename_symm_rename]
  wire_scope_eq := by
    intro wire
    calc
      iso.regions.symm (target.wires wire).scope =
          iso.regions.symm
            (target.wires (iso.wires (iso.wires.symm wire))).scope := by
              exact congrArg
                (fun w => iso.regions.symm (target.wires w).scope)
                (iso.wires.right_inv wire).symm
      _ = iso.regions.symm
            (iso.regions (source.wires (iso.wires.symm wire)).scope) := by
              rw [iso.wire_scope_eq]
      _ = (source.wires (iso.wires.symm wire)).scope := by simp
  wire_endpoints_perm := by
    intro wire
    have h := (iso.wire_endpoints_perm (iso.wires.symm wire)).symm.map
      (CEndpoint.rename iso.nodes.symm)
    have hwire := iso.wires.right_inv wire
    change iso.wires (iso.wires.symm wire) = wire at hwire
    rw [hwire] at h
    have hcancel : ((source.wires (iso.wires.symm wire)).endpoints.map
          (CEndpoint.rename iso.nodes)).map (CEndpoint.rename iso.nodes.symm) =
        (source.wires (iso.wires.symm wire)).endpoints := by
      induction (source.wires (iso.wires.symm wire)).endpoints with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.map_cons, CEndpoint.rename_symm_rename, ih]
    rw [hcancel] at h
    exact h

def trans {first second third : ConcreteDiagram}
    (left : ConcreteIso first second) (right : ConcreteIso second third) :
    ConcreteIso first third where
  regionCount_eq := left.regionCount_eq.trans right.regionCount_eq
  nodeCount_eq := left.nodeCount_eq.trans right.nodeCount_eq
  wireCount_eq := left.wireCount_eq.trans right.wireCount_eq
  regions := left.regions.trans right.regions
  nodes := left.nodes.trans right.nodes
  wires := left.wires.trans right.wires
  root_eq := by simp [left.root_eq, right.root_eq]
  regions_eq := by
    intro region
    calc
      (first.regions region).rename (left.regions.trans right.regions) =
          ((first.regions region).rename left.regions).rename right.regions := by
            rw [CRegion.rename_trans]
      _ = (second.regions (left.regions region)).rename right.regions := by
            rw [left.regions_eq]
      _ = third.regions (right.regions (left.regions region)) := by
            rw [right.regions_eq]
      _ = third.regions ((left.regions.trans right.regions) region) := rfl
  nodes_eq := by
    intro node
    calc
      (first.nodes node).rename (left.regions.trans right.regions) =
          ((first.nodes node).rename left.regions).rename right.regions := by
            rw [CNode.rename_trans]
      _ = (second.nodes (left.nodes node)).rename right.regions := by
            rw [left.nodes_eq]
      _ = third.nodes (right.nodes (left.nodes node)) := by
            rw [right.nodes_eq]
      _ = third.nodes ((left.nodes.trans right.nodes) node) := rfl
  wire_scope_eq := by
    intro wire
    exact (congrArg right.regions (left.wire_scope_eq wire)).trans
      (right.wire_scope_eq (left.wires wire))
  wire_endpoints_perm := by
    intro wire
    have hleft := (left.wire_endpoints_perm wire).map
      (CEndpoint.rename right.nodes)
    have h := hleft.trans (right.wire_endpoints_perm (left.wires wire))
    simpa only [List.map_map, CEndpoint.rename_trans] using h

@[simp] theorem refl_regions (diagram : ConcreteDiagram) :
    (refl diagram).regions = .refl _ := rfl

theorem climb_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (steps : Nat)
    (region : Fin source.regionCount) :
    target.climb steps (iso.regions region) =
      (source.climb steps region).map iso.regions := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      simp only [ConcreteDiagram.climb]
      rw [<- iso.regions_eq region, CRegion.parent?_rename]
      cases hparent : (source.regions region).parent? with
      | none => rfl
      | some parent =>
          simp only [Option.map_some]
          exact ih parent

theorem encloses_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    {ancestor descendant : Fin source.regionCount}
    (h : source.Encloses ancestor descendant) :
    target.Encloses (iso.regions ancestor) (iso.regions descendant) := by
  rcases h with ⟨steps, hsteps⟩
  let targetSteps : Fin (target.regionCount + 1) :=
    Fin.cast (congrArg (fun count => count + 1) iso.regionCount_eq) steps
  refine ⟨targetSteps, ?_⟩
  change target.climb steps.val (iso.regions descendant) = some (iso.regions ancestor)
  rw [iso.climb_transport, hsteps]
  rfl

theorem reachesRoot_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) {region : Fin source.regionCount}
    (h : source.ReachesRoot region) :
    target.ReachesRoot (iso.regions region) := by
  unfold ConcreteDiagram.ReachesRoot at h ⊢
  rw [<- iso.root_eq]
  exact iso.encloses_transport h

theorem endpoint_mem_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) {wire : Fin source.wireCount}
    {endpoint : CEndpoint source.nodeCount}
    (h : endpoint ∈ (source.wires wire).endpoints) :
    endpoint.rename iso.nodes ∈ (target.wires (iso.wires wire)).endpoints := by
  exact (iso.wire_endpoints_perm wire).mem_iff.mp (List.mem_map.mpr ⟨endpoint, h, rfl⟩)

theorem endpoint_mem_reflect {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) {wire : Fin source.wireCount}
    {endpoint : CEndpoint source.nodeCount}
    (h : endpoint.rename iso.nodes ∈
      (target.wires (iso.wires wire)).endpoints) :
    endpoint ∈ (source.wires wire).endpoints := by
  have hmapped : endpoint.rename iso.nodes ∈
      (source.wires wire).endpoints.map (CEndpoint.rename iso.nodes) :=
    (iso.wire_endpoints_perm wire).mem_iff.mpr h
  obtain ⟨other, hother, hrename⟩ := List.mem_map.mp hmapped
  have : other = endpoint := CEndpoint.rename_injective iso.nodes hrename
  simpa [this] using hother

theorem target_region_eq {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin target.regionCount) :
    target.regions region =
      (source.regions (iso.regions.symm region)).rename iso.regions := by
  calc
    target.regions region =
        target.regions (iso.regions (iso.regions.symm region)) :=
      congrArg target.regions (iso.regions.right_inv region).symm
    _ = (source.regions (iso.regions.symm region)).rename iso.regions :=
      (iso.regions_eq (iso.regions.symm region)).symm

theorem target_node_eq {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (node : Fin target.nodeCount) :
    target.nodes node =
      (source.nodes (iso.nodes.symm node)).rename iso.regions := by
  calc
    target.nodes node = target.nodes (iso.nodes (iso.nodes.symm node)) :=
      congrArg target.nodes (iso.nodes.right_inv node).symm
    _ = (source.nodes (iso.nodes.symm node)).rename iso.regions :=
      (iso.nodes_eq (iso.nodes.symm node)).symm

theorem endpoint_mem_pullback {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) {wire : Fin target.wireCount}
    {endpoint : CEndpoint target.nodeCount}
    (h : endpoint ∈ (target.wires wire).endpoints) :
    endpoint.rename iso.nodes.symm ∈
      (source.wires (iso.wires.symm wire)).endpoints := by
  apply iso.endpoint_mem_reflect
  have hwire := iso.wires.right_inv wire
  change iso.wires (iso.wires.symm wire) = wire at hwire
  simpa only [CEndpoint.rename_rename_symm, hwire] using h

theorem endpointOccurs_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) {wire : Fin source.wireCount}
    {endpoint : CEndpoint source.nodeCount}
    (h : source.EndpointOccurs wire endpoint) :
    target.EndpointOccurs (iso.wires wire) (endpoint.rename iso.nodes) :=
  iso.endpoint_mem_transport h

theorem requiresPort_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) {node : Fin source.nodeCount}
    {port : CPort} (h : source.RequiresPort node port) :
    target.RequiresPort (iso.nodes node) port := by
  unfold ConcreteDiagram.RequiresPort at h ⊢
  rw [<- iso.nodes_eq node]
  cases hnode : source.nodes node with
  | term =>
      simp only [hnode] at h
      simpa only [hnode, CNode.rename] using h
  | atom region binder =>
      simp only [hnode] at h
      simp only [CNode.rename]
      rw [<- iso.regions_eq binder]
      cases hbinder : source.regions binder <;>
        simp only [hbinder, CRegion.rename] at h ⊢ <;> exact h
  | named =>
      simp only [hnode] at h
      simpa only [hnode, CNode.rename] using h

theorem rootIsSheet_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.RootIsSheet) :
    target.RootIsSheet := by
  unfold ConcreteDiagram.RootIsSheet at h ⊢
  rw [<- iso.root_eq, <- iso.regions_eq source.root, h]
  rfl

theorem onlyRootIsSheet_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.OnlyRootIsSheet) :
    target.OnlyRootIsSheet := by
  unfold ConcreteDiagram.OnlyRootIsSheet at h ⊢
  intro region hsheet
  have hregions := iso.target_region_eq region
  cases hsource : source.regions (iso.regions.symm region) with
  | sheet =>
      have hroot := h (iso.regions.symm region) hsource
      calc
        region = iso.regions (iso.regions.symm region) :=
          (iso.regions.right_inv region).symm
        _ = iso.regions source.root := congrArg iso.regions hroot
        _ = target.root := iso.root_eq
  | cut parent =>
      rw [hsource] at hregions
      simp only [CRegion.rename] at hregions
      rw [hregions] at hsheet
      contradiction
  | bubble parent arity =>
      rw [hsource] at hregions
      simp only [CRegion.rename] at hregions
      rw [hregions] at hsheet
      contradiction

theorem allRegionsReachRoot_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.AllRegionsReachRoot) :
    target.AllRegionsReachRoot := by
  unfold ConcreteDiagram.AllRegionsReachRoot at h ⊢
  intro region
  have result := iso.reachesRoot_transport (h (iso.regions.symm region))
  have heq := iso.regions.right_inv region
  change iso.regions (iso.regions.symm region) = region at heq
  rw [heq] at result
  exact result

theorem atomBindersAreBubbles_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.AtomBindersAreBubbles) :
    target.AtomBindersAreBubbles := by
  unfold ConcreteDiagram.AtomBindersAreBubbles at h ⊢
  intro node
  have hnodes := iso.target_node_eq node
  cases hs : source.nodes (iso.nodes.symm node) with
  | term =>
      rw [hs] at hnodes
      rw [hnodes]
      trivial
  | named =>
      rw [hs] at hnodes
      rw [hnodes]
      trivial
  | atom region binder =>
      rw [hs] at hnodes
      simp only [CNode.rename] at hnodes
      rw [hnodes]
      have hsource := h (iso.nodes.symm node)
      rw [hs] at hsource
      rcases hsource with ⟨parent, arity, hbinder⟩
      exact ⟨iso.regions parent, arity, by
        rw [<- iso.regions_eq binder, hbinder]
        rfl⟩

theorem atomBindersEnclose_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.AtomBindersEnclose) :
    target.AtomBindersEnclose := by
  unfold ConcreteDiagram.AtomBindersEnclose at h ⊢
  intro node
  have hnodes := iso.target_node_eq node
  cases hs : source.nodes (iso.nodes.symm node) with
  | term =>
      rw [hs] at hnodes
      rw [hnodes]
      trivial
  | named =>
      rw [hs] at hnodes
      rw [hnodes]
      trivial
  | atom region binder =>
      rw [hs] at hnodes
      simp only [CNode.rename] at hnodes
      rw [hnodes]
      have hsource := h (iso.nodes.symm node)
      rw [hs] at hsource
      exact iso.encloses_transport hsource

theorem namedReferencesResolve_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (signature : List Nat)
    (h : source.NamedReferencesResolve signature) :
    target.NamedReferencesResolve signature := by
  unfold ConcreteDiagram.NamedReferencesResolve at h ⊢
  intro node
  have hnodes := iso.target_node_eq node
  cases hs : source.nodes (iso.nodes.symm node) with
  | term =>
      rw [hs] at hnodes
      rw [hnodes]
      trivial
  | atom =>
      rw [hs] at hnodes
      rw [hnodes]
      trivial
  | named region definition arity =>
      rw [hs] at hnodes
      simp only [CNode.rename] at hnodes
      rw [hnodes]
      have hsource := h (iso.nodes.symm node)
      rw [hs] at hsource
      exact hsource

theorem endpointsAreValid_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.EndpointsAreValid) :
    target.EndpointsAreValid := by
  unfold ConcreteDiagram.EndpointsAreValid at h ⊢
  intro wire endpoint hmem
  have sourceMem := iso.endpoint_mem_pullback hmem
  have required := iso.requiresPort_transport
    (h (iso.wires.symm wire) (endpoint.rename iso.nodes.symm) sourceMem)
  have hnode := iso.nodes.right_inv endpoint.node
  change iso.nodes (iso.nodes.symm endpoint.node) = endpoint.node at hnode
  change target.RequiresPort
    (iso.nodes (iso.nodes.symm endpoint.node)) endpoint.port at required
  rw [hnode] at required
  exact required

theorem endpointsAreNodup_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.EndpointsAreNodup) :
    target.EndpointsAreNodup := by
  unfold ConcreteDiagram.EndpointsAreNodup at h ⊢
  intro wire
  let sourceWire := iso.wires.symm wire
  have mappedNodup : ((source.wires sourceWire).endpoints.map
      (CEndpoint.rename iso.nodes)).Nodup :=
    (h sourceWire).map (CEndpoint.rename iso.nodes)
      (fun _ _ hne heq => hne (CEndpoint.rename_injective iso.nodes heq))
  have targetNodup := (iso.wire_endpoints_perm sourceWire).nodup_iff.mp mappedNodup
  have hwire := iso.wires.right_inv wire
  change iso.wires sourceWire = wire at hwire
  simpa only [hwire] using targetNodup

theorem wireEndpointsAreDisjoint_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.WireEndpointsAreDisjoint) :
    target.WireEndpointsAreDisjoint := by
  unfold ConcreteDiagram.WireEndpointsAreDisjoint at h ⊢
  simp only [bne_iff_ne] at h ⊢
  intro wire₁ wire₂ hne endpoint hmem₁
  rw [Bool.not_eq_true']
  apply decide_eq_false
  intro hmem₂
  let sourceWire₁ := iso.wires.symm wire₁
  let sourceWire₂ := iso.wires.symm wire₂
  let sourceEndpoint := endpoint.rename iso.nodes.symm
  have sourceNe : sourceWire₁ ≠ sourceWire₂ := by
    intro heq
    apply hne
    have hmapped := congrArg iso.wires heq
    have hleft := iso.wires.right_inv wire₁
    have hright := iso.wires.right_inv wire₂
    change iso.wires sourceWire₁ = wire₁ at hleft
    change iso.wires sourceWire₂ = wire₂ at hright
    rw [hleft, hright] at hmapped
    exact hmapped
  have hbool := h sourceWire₁ sourceWire₂ sourceNe sourceEndpoint
    (iso.endpoint_mem_pullback hmem₁)
  rw [Bool.not_eq_true'] at hbool
  exact (of_decide_eq_false hbool) (iso.endpoint_mem_pullback hmem₂)

theorem requiredPortsAreCovered_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.RequiredPortsAreCovered) :
    target.RequiredPortsAreCovered := by
  unfold ConcreteDiagram.RequiredPortsAreCovered at h ⊢
  intro node
  let sourceNode := iso.nodes.symm node
  have hnode : iso.nodes sourceNode = node := iso.nodes.right_inv node
  have covered {port : CPort}
      (hcovered : exists wire,
        source.EndpointOccurs wire ⟨sourceNode, port⟩) :
      exists wire, target.EndpointOccurs wire ⟨node, port⟩ := by
    rcases hcovered with ⟨wire, hwire⟩
    refine ⟨iso.wires wire, ?_⟩
    have mapped := iso.endpointOccurs_transport hwire
    simpa only [CEndpoint.rename, hnode] using mapped
  have hnodes := iso.target_node_eq node
  cases hs : source.nodes sourceNode with
  | term region freePorts term =>
      rw [hs] at hnodes
      simp only [CNode.rename] at hnodes
      rw [hnodes]
      simp only
      have hsource := h sourceNode
      rw [hs] at hsource
      exact ⟨covered hsource.1, fun index => covered (hsource.2 index)⟩
  | atom region binder =>
      rw [hs] at hnodes
      simp only [CNode.rename] at hnodes
      rw [hnodes]
      simp only
      have hsource := h sourceNode
      rw [hs] at hsource
      simp only at hsource
      have hbinderTarget := iso.regions_eq binder
      cases hbinder : source.regions binder with
      | sheet =>
          rw [hbinder] at hbinderTarget
          simp only [CRegion.rename] at hbinderTarget
          rw [<- hbinderTarget]
          trivial
      | cut parent =>
          rw [hbinder] at hbinderTarget
          simp only [CRegion.rename] at hbinderTarget
          rw [<- hbinderTarget]
          trivial
      | bubble parent arity =>
          rw [hbinder] at hbinderTarget
          simp only [CRegion.rename] at hbinderTarget
          rw [<- hbinderTarget]
          rw [hbinder] at hsource
          intro index
          exact covered (hsource index)
  | named region definition arity =>
      rw [hs] at hnodes
      simp only [CNode.rename] at hnodes
      rw [hnodes]
      have hsource := h sourceNode
      rw [hs] at hsource
      intro index
      exact covered (hsource index)

theorem wireScopesEnclose_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (h : source.WireScopesEnclose) :
    target.WireScopesEnclose := by
  unfold ConcreteDiagram.WireScopesEnclose at h ⊢
  intro wire endpoint hmem
  let sourceWire := iso.wires.symm wire
  let sourceEndpoint := endpoint.rename iso.nodes.symm
  have sourceMem : sourceEndpoint ∈ (source.wires sourceWire).endpoints :=
    iso.endpoint_mem_pullback hmem
  have hencloses := iso.encloses_transport (h sourceWire sourceEndpoint sourceMem)
  rw [iso.wire_scope_eq sourceWire] at hencloses
  have nodeRegion := CNode.region_rename iso.regions (source.nodes sourceEndpoint.node)
  rw [iso.nodes_eq sourceEndpoint.node] at nodeRegion
  have hwire := iso.wires.right_inv wire
  change iso.wires sourceWire = wire at hwire
  rw [hwire] at hencloses
  have hnode := iso.nodes.right_inv endpoint.node
  change iso.nodes sourceEndpoint.node = endpoint.node at hnode
  rw [hnode] at nodeRegion
  rw [<- nodeRegion] at hencloses
  exact hencloses

def wellFormed_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) {signature : List Nat}
    (h : source.WellFormed signature) : target.WellFormed signature where
  root_is_sheet := iso.rootIsSheet_transport h.root_is_sheet
  only_root_is_sheet := iso.onlyRootIsSheet_transport h.only_root_is_sheet
  all_regions_reach_root :=
    iso.allRegionsReachRoot_transport h.all_regions_reach_root
  atom_binders_are_bubbles :=
    iso.atomBindersAreBubbles_transport h.atom_binders_are_bubbles
  atom_binders_enclose :=
    iso.atomBindersEnclose_transport h.atom_binders_enclose
  named_references_resolve :=
    iso.namedReferencesResolve_transport signature h.named_references_resolve
  endpoints_are_valid :=
    iso.endpointsAreValid_transport h.endpoints_are_valid
  endpoints_are_nodup :=
    iso.endpointsAreNodup_transport h.endpoints_are_nodup
  wire_endpoints_are_disjoint :=
    iso.wireEndpointsAreDisjoint_transport h.wire_endpoints_are_disjoint
  required_ports_are_covered :=
    iso.requiredPortsAreCovered_transport h.required_ports_are_covered
  wire_scopes_enclose :=
    iso.wireScopesEnclose_transport h.wire_scopes_enclose

def checked_transport {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) {signature : List Nat}
    (checked : CheckedDiagram signature) (hsource : checked.val = source) :
    CheckedDiagram signature := by
  subst source
  exact ⟨target, iso.wellFormed_transport checked.property⟩

end ConcreteIso

namespace ConcreteExamples

def nodeReverse : FiniteEquiv (Fin 2) (Fin 2) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

@[simp] theorem nodeReverse_apply (node : Fin 2) :
    nodeReverse node = Fin.rev node := rfl

def validNestedRelabeled : ConcreteDiagram where
  regionCount := validNested.regionCount
  nodeCount := validNested.nodeCount
  wireCount := validNested.wireCount
  root := validNested.root
  regions := validNested.regions
  nodes := fun node =>
    (validNested.nodes (nodeReverse.invFun node)).rename (.refl _)
  wires := fun wire => {
    scope := (validNested.wires wire).scope
    endpoints := ((validNested.wires wire).endpoints.map
      (CEndpoint.rename nodeReverse)).reverse
  }

def validNestedRelabeledIso :
    ConcreteIso validNested validNestedRelabeled where
  regionCount_eq := rfl
  nodeCount_eq := rfl
  wireCount_eq := rfl
  regions := .refl _
  nodes := nodeReverse
  wires := .refl _
  root_eq := rfl
  regions_eq := by simp [validNestedRelabeled]
  nodes_eq := by
    intro node
    change (validNested.nodes node).rename (.refl _) =
      (validNested.nodes (Fin.rev (Fin.rev node))).rename (.refl _)
    rw [Fin.rev_rev]
  wire_scope_eq := by simp [validNestedRelabeled]
  wire_endpoints_perm := by
    intro wire
    exact (List.reverse_perm _).symm

theorem validNestedRelabeled_nontrivial :
    (validNestedRelabeledIso.nodes (0 : Fin 2)).val = 1 := by
  rfl

theorem validNestedRelabeled_wellFormed :
    validNestedRelabeled.WellFormed [] :=
  validNestedRelabeledIso.wellFormed_transport
    (checkWellFormed_iff.mp validNested_check)

def validNestedRelabeledChecked : CheckedDiagram [] :=
  validNestedRelabeledIso.checked_transport
    ⟨validNested, checkWellFormed_iff.mp validNested_check⟩ rfl

theorem validNestedRelabeled_checked_transport :
    validNestedRelabeledChecked.val = validNestedRelabeled := rfl

end ConcreteExamples

end VisualProof.Diagram
