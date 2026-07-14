import VisualProof.Diagram.Concrete.Subgraph.Selection
import VisualProof.Diagram.Concrete.WellFormed
import VisualProof.Diagram.Concrete.Open
import VisualProof.Diagram.Concrete.Elaboration.Context

namespace VisualProof.Diagram

open VisualProof.Data.Finite

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

/-- Any two regions on one concrete parent chain are comparable. -/
theorem ConcreteDiagram.enclosingRegions_comparable {d : ConcreteDiagram}
    {first second descendant : Fin d.regionCount}
    (hfirst : d.Encloses first descendant)
    (hsecond : d.Encloses second descendant) :
    d.Encloses first second ∨ d.Encloses second first := by
  obtain ⟨firstSteps, hfirst⟩ := hfirst
  obtain ⟨secondSteps, hsecond⟩ := hsecond
  by_cases hle : firstSteps.val ≤ secondSteps.val
  · right
    refine ⟨⟨secondSteps.val - firstSteps.val, by omega⟩, ?_⟩
    exact climb_cancel_prefix hle hfirst hsecond
  · left
    have hreverse : secondSteps.val ≤ firstSteps.val := by omega
    refine ⟨⟨firstSteps.val - secondSteps.val, by omega⟩, ?_⟩
    exact climb_cancel_prefix hreverse hsecond hfirst

namespace CheckedSelection

/-- A selected atom uses this binder, but the binder is outside the selection. -/
def UsesExternalBinder (selection : CheckedSelection d)
    (binder : Fin d.regionCount) : Prop :=
  binder ∉ selection.selectedRegions ∧
    ∃ node, node ∈ selection.selectedNodes ∧
      match d.nodes node with
      | .atom _ candidate => candidate = binder
      | _ => False

instance (selection : CheckedSelection d) (binder : Fin d.regionCount) :
    Decidable (selection.UsesExternalBinder binder) := by
  unfold UsesExternalBinder
  let P : Fin d.nodeCount → Prop := fun node =>
    node ∈ selection.selectedNodes ∧
      match d.nodes node with
      | .atom _ candidate => candidate = binder
      | _ => False
  letI : DecidablePred P := fun node => by
    dsimp [P]
    cases d.nodes node <;> infer_instance
  change Decidable (binder ∉ selection.selectedRegions ∧ ∃ node, P node)
  infer_instance

/-- The anchor-to-root chain, including the anchor and root, nearest first. -/
def anchorChainInnerFirst (selection : CheckedSelection d) :
    List (Fin d.regionCount) :=
  (allFin (d.regionCount + 1)).filterMap fun steps =>
    d.climb steps.val selection.val.anchor

@[simp] theorem mem_anchorChainInnerFirst (selection : CheckedSelection d)
    (binder : Fin d.regionCount) :
    binder ∈ selection.anchorChainInnerFirst ↔
      d.Encloses binder selection.val.anchor := by
  simp [anchorChainInnerFirst, ConcreteDiagram.Encloses]

/--
Distinct external binders in outermost-first ancestry order. On a checked host,
every used external atom binder occurs on this chain.
-/
def externalBinders (selection : CheckedSelection d) :
    List (Fin d.regionCount) :=
  (selection.anchorChainInnerFirst.reverse.filter fun binder =>
    decide (selection.UsesExternalBinder binder)).eraseDups

theorem externalBinders_nodup (selection : CheckedSelection d) :
    selection.externalBinders.Nodup := by
  exact eraseDups_nodup _

theorem mem_externalBinders_anchorChain (selection : CheckedSelection d)
    {binder : Fin d.regionCount} (hmember : binder ∈ selection.externalBinders) :
    binder ∈ selection.anchorChainInnerFirst := by
  simp only [externalBinders, List.mem_eraseDups] at hmember
  exact List.mem_reverse.mp (List.mem_filter.mp hmember).1

theorem mem_externalBinders_uses (selection : CheckedSelection d)
    {binder : Fin d.regionCount} (hmember : binder ∈ selection.externalBinders) :
    selection.UsesExternalBinder binder := by
  simp only [externalBinders, List.mem_eraseDups] at hmember
  exact of_decide_eq_true ((List.mem_filter.mp hmember).2)

/-- Every genuinely external selected-atom binder encloses the selection anchor. -/
theorem usesExternalBinder_encloses_anchor
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) {binder : Fin host.val.regionCount}
    (huses : selection.UsesExternalBinder binder) :
    host.val.Encloses binder selection.val.anchor := by
  obtain ⟨hnotSelected, node, hselectedNode, hatom⟩ := huses
  cases hnode : host.val.nodes node with
  | term region freePorts term => simp [hnode] at hatom
  | named region definition arity => simp [hnode] at hatom
  | atom region candidate =>
      simp only [hnode] at hatom
      subst candidate
      have hbinderEncloses := host.property.atom_binders_enclose node
      simp only [hnode] at hbinderEncloses
      have hselected := (selection.mem_selectedNodes node).1 hselectedNode
      rcases hselected with hdirect | hsubtree
      · have howner := selection.property.directNodes_at_anchor node hdirect
        simp only [hnode, CNode.region] at howner
        rwa [howner] at hbinderEncloses
      · obtain ⟨child, hchild, hchildEncloses⟩ := hsubtree
        simp only [hnode, CNode.region] at hchildEncloses
        rcases host.val.enclosingRegions_comparable hbinderEncloses
            hchildEncloses with hbinderChild | hchildBinder
        · have hparent := selection.property.childRoots_direct child hchild
          rcases ConcreteElaboration.encloses_direct_child hparent hbinderChild with
            heq | hbinderAnchor
          · subst binder
            exact False.elim (hnotSelected
              ((selection.mem_selectedRegions child).2
                ⟨child, hchild, ConcreteDiagram.Encloses.refl host.val child⟩))
          · exact hbinderAnchor
        · exact False.elim (hnotSelected
            ((selection.mem_selectedRegions binder).2
              ⟨child, hchild, hchildBinder⟩))

/-- The generated target list contains exactly the external binders actually used. -/
theorem mem_externalBinders_iff_uses
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (binder : Fin host.val.regionCount) :
    binder ∈ selection.externalBinders ↔
      selection.UsesExternalBinder binder := by
  constructor
  · exact selection.mem_externalBinders_uses
  · intro huses
    have hchain : binder ∈ selection.anchorChainInnerFirst :=
      (selection.mem_anchorChainInnerFirst binder).2
        (selection.usesExternalBinder_encloses_anchor host huses)
    simp only [externalBinders, List.mem_eraseDups, List.mem_filter]
    exact ⟨List.mem_reverse.mpr hchain, decide_eq_true huses⟩

/-- External binder targets form one lexical ancestry chain. -/
theorem externalBinders_comparable
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    {first second : Fin host.val.regionCount}
    (hfirst : first ∈ selection.externalBinders)
    (hsecond : second ∈ selection.externalBinders) :
    host.val.Encloses first second ∨ host.val.Encloses second first := by
  exact host.val.enclosingRegions_comparable
    (selection.usesExternalBinder_encloses_anchor host
      ((selection.mem_externalBinders_iff_uses host first).1 hfirst))
    (selection.usesExternalBinder_encloses_anchor host
      ((selection.mem_externalBinders_iff_uses host second).1 hsecond))

end CheckedSelection

/-- Arithmetic layout of a generated fragment's administrative and material blocks. -/
structure FragmentLayout (d : ConcreteDiagram) (selection : CheckedSelection d) where
  externalBinders : List (Fin d.regionCount) := selection.externalBinders
  externalBinders_exact : externalBinders = selection.externalBinders := by rfl

namespace FragmentLayout

def proxyCount (layout : FragmentLayout d selection) : Nat :=
  layout.externalBinders.length

def materialRegionCount (_layout : FragmentLayout d selection) : Nat :=
  selection.selectedRegions.length

def regionCount (layout : FragmentLayout d selection) : Nat :=
  1 + (layout.proxyCount + layout.materialRegionCount)

def nodeCount (_layout : FragmentLayout d selection) : Nat :=
  selection.selectedNodes.length

def internalWireCount (_layout : FragmentLayout d selection) : Nat :=
  selection.internalWires.length

def boundaryWireCount (_layout : FragmentLayout d selection) : Nat :=
  selection.touchingWires.length

def wireCount (layout : FragmentLayout d selection) : Nat :=
  layout.internalWireCount + layout.boundaryWireCount

theorem externalBinders_nodup (layout : FragmentLayout d selection) :
    layout.externalBinders.Nodup := by
  rw [layout.externalBinders_exact]
  exact selection.externalBinders_nodup

theorem externalBinderTarget_injective (layout : FragmentLayout d selection) :
    Function.Injective layout.externalBinders.get := by
  intro left right heq
  apply Fin.ext
  exact (List.getElem_inj layout.externalBinders_nodup).mp (by
    simpa only [List.get_eq_getElem] using heq)

def root (layout : FragmentLayout d selection) : Fin layout.regionCount :=
  ⟨0, by unfold regionCount; omega⟩

def proxy (layout : FragmentLayout d selection)
    (index : Fin layout.proxyCount) : Fin layout.regionCount :=
  ⟨1 + index.val, by
    simp only [regionCount, proxyCount, materialRegionCount]
    omega⟩

def materialRegion (layout : FragmentLayout d selection)
    (index : Fin layout.materialRegionCount) : Fin layout.regionCount :=
  ⟨1 + layout.proxyCount + index.val, by
    simp only [regionCount, materialRegionCount]
    omega⟩

def bodyContainer (layout : FragmentLayout d selection) :
    Fin layout.regionCount :=
  if h : layout.proxyCount = 0 then
    layout.root
  else
    layout.proxy ⟨layout.proxyCount - 1, by omega⟩

def internalWire (layout : FragmentLayout d selection)
    (index : Fin layout.internalWireCount) : Fin layout.wireCount :=
  Fin.castAdd layout.boundaryWireCount index

def boundaryWire (layout : FragmentLayout d selection)
    (index : Fin layout.boundaryWireCount) : Fin layout.wireCount :=
  Fin.natAdd layout.internalWireCount index

theorem proxy_injective (layout : FragmentLayout d selection) :
    Function.Injective layout.proxy := by
  intro left right heq
  apply Fin.ext
  have := congrArg Fin.val heq
  simpa [proxy] using this

theorem materialRegion_injective (layout : FragmentLayout d selection) :
    Function.Injective layout.materialRegion := by
  intro left right heq
  apply Fin.ext
  have := congrArg Fin.val heq
  simpa [materialRegion] using this

theorem proxy_eq_succ_castAdd (layout : FragmentLayout d selection)
    (index : Fin layout.proxyCount) :
    layout.proxy index =
      Fin.cast (by simp [regionCount]; omega)
        (Fin.succ (Fin.castAdd layout.materialRegionCount index)) := by
  apply Fin.ext
  simp [proxy]
  omega

theorem materialRegion_eq_succ_natAdd (layout : FragmentLayout d selection)
    (index : Fin layout.materialRegionCount) :
    layout.materialRegion index =
      Fin.cast (by simp [regionCount]; omega)
        (Fin.succ (Fin.natAdd layout.proxyCount index)) := by
  apply Fin.ext
  simp [materialRegion]
  omega

theorem proxy_ne_root (layout : FragmentLayout d selection)
    (index : Fin layout.proxyCount) : layout.proxy index ≠ layout.root := by
  intro heq
  have := congrArg Fin.val heq
  simp only [proxy, root] at this
  omega

theorem materialRegion_ne_root (layout : FragmentLayout d selection)
    (index : Fin layout.materialRegionCount) :
    layout.materialRegion index ≠ layout.root := by
  intro heq
  have := congrArg Fin.val heq
  simp only [materialRegion, root] at this
  omega

theorem proxy_ne_materialRegion (layout : FragmentLayout d selection)
    (proxy : Fin layout.proxyCount)
    (material : Fin layout.materialRegionCount) :
    layout.proxy proxy ≠ layout.materialRegion material := by
  intro heq
  have := congrArg Fin.val heq
  simp only [FragmentLayout.proxy, FragmentLayout.materialRegion] at this
  omega

theorem bodyContainer_eq_root_of_proxyCount_eq_zero
    (layout : FragmentLayout d selection) (hzero : layout.proxyCount = 0) :
    layout.bodyContainer = layout.root := by
  simp [bodyContainer, hzero]

theorem bodyContainer_eq_terminal_of_proxyCount_ne_zero
    (layout : FragmentLayout d selection) (hnonzero : layout.proxyCount ≠ 0) :
    layout.bodyContainer =
      layout.proxy ⟨layout.proxyCount - 1, by omega⟩ := by
  simp [bodyContainer, hnonzero]

theorem bodyContainer_ne_root_of_proxyCount_ne_zero
    (layout : FragmentLayout d selection) (hnonzero : layout.proxyCount ≠ 0) :
    layout.bodyContainer ≠ layout.root := by
  rw [layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hnonzero]
  exact layout.proxy_ne_root _

theorem bodyContainer_ne_nonterminalProxy
    (layout : FragmentLayout d selection) (index : Fin layout.proxyCount)
    (hnonterminal : index.val + 1 < layout.proxyCount) :
    layout.bodyContainer ≠ layout.proxy index := by
  have hnonzero : layout.proxyCount ≠ 0 := by omega
  rw [layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hnonzero]
  intro heq
  have hindex := layout.proxy_injective heq
  have hvals := congrArg Fin.val hindex
  simp only at hvals
  omega

@[simp] theorem boundaryWire_val (layout : FragmentLayout d selection)
    (index : Fin layout.boundaryWireCount) :
    (layout.boundaryWire index).val = layout.internalWireCount + index.val := rfl

end FragmentLayout

/--
An explicit designation of a nested ordinary-bubble prefix and its effective
body container. The graph shape alone never designates a bubble as a proxy.
-/
structure BinderSpine (diagram : ConcreteDiagram) where
  proxyCount : Nat
  proxy : Fin proxyCount → Fin diagram.regionCount
  arity : Fin proxyCount → Nat
  bodyContainer : Fin diagram.regionCount
  proxy_injective : Function.Injective proxy
  proxy_ne_root : ∀ index, proxy index ≠ diagram.root
  body_eq_root_of_empty : proxyCount = 0 → bodyContainer = diagram.root
  body_eq_terminal_of_nonempty : ∀ h : proxyCount ≠ 0,
    bodyContainer = proxy ⟨proxyCount - 1, by omega⟩
  proxy_region : ∀ index,
    diagram.regions (proxy index) =
      .bubble
        (if _hzero : index.val = 0 then diagram.root
          else proxy ⟨index.val - 1, by omega⟩)
        (arity index)

namespace BinderSpine

/-- Regions with material provenance: neither the fresh sheet nor a proxy. -/
def IsMaterialRegion (spine : BinderSpine diagram)
    (region : Fin diagram.regionCount) : Prop :=
  region ≠ diagram.root ∧ ∀ index, region ≠ spine.proxy index

instance (spine : BinderSpine diagram) (region : Fin diagram.regionCount) :
    Decidable (spine.IsMaterialRegion region) := by
  unfold IsMaterialRegion
  infer_instance

/-- Canonical dense enumeration of the pattern regions eligible for matching. -/
def materialRegions (spine : BinderSpine diagram) :
    List (Fin diagram.regionCount) :=
  filterFin fun region => decide (spine.IsMaterialRegion region)

@[simp] theorem mem_materialRegions (spine : BinderSpine diagram)
    (region : Fin diagram.regionCount) :
    region ∈ spine.materialRegions ↔ spine.IsMaterialRegion region := by
  simp [materialRegions]

theorem materialRegions_nodup (spine : BinderSpine diagram) :
    spine.materialRegions.Nodup :=
  filterFin_nodup _

theorem root_not_mem_materialRegions (spine : BinderSpine diagram) :
    diagram.root ∉ spine.materialRegions := by
  simp [IsMaterialRegion]

theorem proxy_not_mem_materialRegions (spine : BinderSpine diagram)
    (index : Fin spine.proxyCount) :
    spine.proxy index ∉ spine.materialRegions := by
  intro hmember
  exact ((spine.mem_materialRegions (spine.proxy index)).1 hmember).2 index rfl

/--
The semantic side conditions that make a designated spine a terminal-body
interface rather than an arbitrary list of bubbles.
-/
structure TerminalBodyContract (openDiagram : OpenConcreteDiagram)
    (spine : BinderSpine openDiagram.diagram) : Prop where
  root_direct_child : ∀ hnonzero : spine.proxyCount ≠ 0,
    ∀ region,
      (openDiagram.diagram.regions region).parent? =
          some openDiagram.diagram.root →
        region = spine.proxy ⟨0, Nat.pos_of_ne_zero hnonzero⟩
  nonterminal_direct_child :
    ∀ (proxy : Fin spine.proxyCount)
      (hnonterminal : proxy.val + 1 < spine.proxyCount),
      ∀ region,
        (openDiagram.diagram.regions region).parent? =
            some (spine.proxy proxy) →
          region = spine.proxy ⟨proxy.val + 1, hnonterminal⟩
  root_has_no_nodes : spine.proxyCount ≠ 0 →
    ∀ node, (openDiagram.diagram.nodes node).region ≠ openDiagram.diagram.root
  nonterminal_has_no_nodes :
    ∀ (proxy : Fin spine.proxyCount), proxy.val + 1 < spine.proxyCount →
      ∀ node,
        (openDiagram.diagram.nodes node).region ≠ spine.proxy proxy
  root_has_no_nonboundary_wires : spine.proxyCount ≠ 0 →
    ∀ wire, wire ∉ openDiagram.boundary →
      (openDiagram.diagram.wires wire).scope ≠ openDiagram.diagram.root
  nonterminal_has_no_nonboundary_wires :
    ∀ (proxy : Fin spine.proxyCount), proxy.val + 1 < spine.proxyCount →
      ∀ wire, wire ∉ openDiagram.boundary →
        (openDiagram.diagram.wires wire).scope ≠ spine.proxy proxy
  boundary_is_root_scoped :
    ∀ wire, wire ∈ openDiagram.boundary →
      (openDiagram.diagram.wires wire).scope = openDiagram.diagram.root

end BinderSpine

namespace ConcreteDiagram

def fragmentParent (layout : FragmentLayout d selection)
    (parent : Fin d.regionCount) : Fin layout.regionCount :=
  if parent = selection.val.anchor then
    layout.bodyContainer
  else
    match indexOf? selection.selectedRegions parent with
    | some index => layout.materialRegion index
    | none => layout.bodyContainer

def fragmentBinder (layout : FragmentLayout d selection)
    (binder : Fin d.regionCount) : Fin layout.regionCount :=
  match indexOf? selection.selectedRegions binder with
  | some index => layout.materialRegion index
  | none =>
      match indexOf? layout.externalBinders binder with
      | some index => layout.proxy index
      | none => layout.bodyContainer

private def proxyParent (layout : FragmentLayout d selection)
    (index : Fin layout.proxyCount) : Fin layout.regionCount :=
  if hzero : index.val = 0 then
    layout.root
  else
    layout.proxy ⟨index.val - 1, by omega⟩

private def proxyArity (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection)
    (index : Fin layout.proxyCount) : Nat :=
  d.binderArity? (layout.externalBinders.get index) |>.getD 0

private def fragmentProxyRegion (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection)
    (index : Fin layout.proxyCount) : CRegion layout.regionCount :=
  .bubble (proxyParent layout index) (d.proxyArity selection layout index)

private def fragmentMaterialRegion (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection)
    (index : Fin layout.materialRegionCount) : CRegion layout.regionCount :=
  match d.regions (selection.selectedRegions.get index) with
  | .sheet => .cut layout.bodyContainer
  | .cut parent => .cut (fragmentParent layout parent)
  | .bubble parent arity => .bubble (fragmentParent layout parent) arity

private def fragmentRegion (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection) :
    Fin layout.regionCount → CRegion layout.regionCount :=
  fun region =>
    Fin.cases CRegion.sheet
      (fun rest => Fin.addCases
        (d.fragmentProxyRegion selection layout)
        (d.fragmentMaterialRegion selection layout)
        rest)
      (Fin.cast (by
        simp only [FragmentLayout.regionCount]
        omega) region)

private def fragmentNode (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection)
    (index : Fin layout.nodeCount) : CNode layout.regionCount :=
  match d.nodes (selection.selectedNodes.get index) with
  | .term region freePorts term =>
      .term (fragmentParent layout region) freePorts term
  | .atom region binder =>
      .atom (fragmentParent layout region) (fragmentBinder layout binder)
  | .named region definition arity =>
      .named (fragmentParent layout region) definition arity

private def fragmentEndpoint? (selection : CheckedSelection d)
    (endpoint : CEndpoint d.nodeCount) :
    Option (CEndpoint selection.selectedNodes.length) :=
  (indexOf? selection.selectedNodes endpoint.node).map fun node =>
    { node, port := endpoint.port }

private def fragmentEndpoints (d : ConcreteDiagram)
    (selection : CheckedSelection d) (wire : Fin d.wireCount) :
    List (CEndpoint selection.selectedNodes.length) :=
  (d.wires wire).endpoints.filterMap (fragmentEndpoint? selection)

private def fragmentInternalWire (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection)
    (index : Fin layout.internalWireCount) :
    CWire layout.regionCount layout.nodeCount :=
  let wire := selection.internalWires.get index
  {
    scope := fragmentParent layout (d.wires wire).scope
    endpoints := d.fragmentEndpoints selection wire
  }

private def fragmentBoundaryWire (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection)
    (index : Fin layout.boundaryWireCount) :
    CWire layout.regionCount layout.nodeCount :=
  let wire := selection.touchingWires.get index
  {
    scope := layout.root
    endpoints := d.fragmentEndpoints selection wire
  }

private def fragmentWire (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection) :
    Fin layout.wireCount → CWire layout.regionCount layout.nodeCount :=
  Fin.addCases
    (d.fragmentInternalWire selection layout)
    (d.fragmentBoundaryWire selection layout)

/-- The ordinary concrete graph underlying extraction. -/
def extractDiagramRaw (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection := {}) : ConcreteDiagram where
  regionCount := layout.regionCount
  nodeCount := layout.nodeCount
  wireCount := layout.wireCount
  root := layout.root
  regions := d.fragmentRegion selection layout
  nodes := d.fragmentNode selection layout
  wires := d.fragmentWire selection layout

/-- One ordered boundary position per touching host wire. -/
def extractBoundaryRaw (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection := {}) :
    List (Fin (d.extractDiagramRaw selection layout).wireCount) :=
  List.ofFn layout.boundaryWire

def extractOpenRaw (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection := {}) : OpenConcreteDiagram where
  diagram := d.extractDiagramRaw selection layout
  boundary := d.extractBoundaryRaw selection layout

@[simp] theorem extractDiagramRaw_root_region (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection) :
    (d.extractDiagramRaw selection layout).regions layout.root = .sheet := by
  simp [extractDiagramRaw, fragmentRegion, FragmentLayout.root]

theorem extractDiagramRaw_proxy_region (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection)
    (index : Fin layout.proxyCount) :
    (d.extractDiagramRaw selection layout).regions (layout.proxy index) =
      .bubble (proxyParent layout index) (d.proxyArity selection layout index) := by
  rw [layout.proxy_eq_succ_castAdd]
  simp [extractDiagramRaw, fragmentRegion, fragmentProxyRegion]

theorem extractDiagramRaw_materialRegion (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection)
    (index : Fin layout.materialRegionCount) :
    (d.extractDiagramRaw selection layout).regions
        (layout.materialRegion index) =
      d.fragmentMaterialRegion selection layout index := by
  rw [layout.materialRegion_eq_succ_natAdd]
  simp [extractDiagramRaw, fragmentRegion]

/-- The extraction-generated terminal-body binder interface. -/
def extractedBinderSpine (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection := {}) :
    BinderSpine (d.extractDiagramRaw selection layout) where
  proxyCount := layout.proxyCount
  proxy := layout.proxy
  arity := d.proxyArity selection layout
  bodyContainer := layout.bodyContainer
  proxy_injective := layout.proxy_injective
  proxy_ne_root := by
    intro index
    exact layout.proxy_ne_root index
  body_eq_root_of_empty := by
    intro hzero
    exact layout.bodyContainer_eq_root_of_proxyCount_eq_zero hzero
  body_eq_terminal_of_nonempty := by
    intro hnonzero
    exact layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hnonzero
  proxy_region := by
    intro index
    rw [d.extractDiagramRaw_proxy_region selection layout index]
    rfl

/-- A binder copied with material provenance is renamed to that material region. -/
theorem fragmentBinder_selectedRegion
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (index : Fin layout.materialRegionCount) :
    d.fragmentBinder layout (selection.selectedRegions.get index) =
      layout.materialRegion index := by
  unfold fragmentBinder
  rw [indexOf?_get_eq_some_of_nodup selection.selectedRegions_nodup]

/-- An external binder is renamed to its unique aligned proxy. -/
theorem fragmentBinder_externalBinder
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (index : Fin layout.proxyCount) :
    host.val.fragmentBinder layout (layout.externalBinders.get index) =
      layout.proxy index := by
  have hmemberLayout : layout.externalBinders.get index ∈
      layout.externalBinders := List.get_mem _ _
  have hmemberSelection : layout.externalBinders.get index ∈
      selection.externalBinders := by
    rw [← layout.externalBinders_exact]
    exact hmemberLayout
  have hnotSelected :=
    ((selection.mem_externalBinders_iff_uses host _).1 hmemberSelection).1
  unfold fragmentBinder
  cases hselected : indexOf? selection.selectedRegions
      (layout.externalBinders.get index) with
  | some found =>
      exfalso
      apply hnotSelected
      rw [← indexOf?_sound hselected]
      exact List.get_mem _ found
  | none =>
      simp only
      rw [indexOf?_get_eq_some_of_nodup layout.externalBinders_nodup]

/-- Selected atoms using external binders point to exactly the aligned proxy. -/
theorem extractDiagramRaw_externalAtom
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (node : Fin layout.nodeCount) (proxy : Fin layout.proxyCount)
    (region : Fin host.val.regionCount)
    (hnode : host.val.nodes (selection.selectedNodes.get node) =
      .atom region (layout.externalBinders.get proxy)) :
    (host.val.extractDiagramRaw selection layout).nodes node =
      .atom (host.val.fragmentParent layout region) (layout.proxy proxy) := by
  change host.val.fragmentNode selection layout node = _
  unfold fragmentNode
  rw [hnode]
  change CNode.atom (host.val.fragmentParent layout region)
      (host.val.fragmentBinder layout (layout.externalBinders.get proxy)) = _
  rw [ConcreteDiagram.fragmentBinder_externalBinder host selection layout proxy]
  rfl

/-- In an extracted fragment, material support is exactly the copied-region block. -/
theorem extractedBinderSpine_isMaterialRegion_iff
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (region : Fin (d.extractDiagramRaw selection layout).regionCount) :
    (d.extractedBinderSpine selection layout).IsMaterialRegion region ↔
      ∃ index : Fin layout.materialRegionCount,
        layout.materialRegion index = region := by
  constructor
  · rintro ⟨hneRoot, hneProxy⟩
    have hpositive : 0 < region.val := by
      by_cases hzero : region.val = 0
      · exfalso
        apply hneRoot
        apply Fin.ext
        simpa [extractDiagramRaw, FragmentLayout.root] using hzero
      · omega
    have hpastProxies : 1 + layout.proxyCount ≤ region.val := by
      by_cases hpast : 1 + layout.proxyCount ≤ region.val
      · exact hpast
      · exfalso
        let index : Fin layout.proxyCount :=
          ⟨region.val - 1, by omega⟩
        apply hneProxy index
        apply Fin.ext
        simp [extractedBinderSpine, FragmentLayout.proxy, index]
        omega
    let index : Fin layout.materialRegionCount :=
      ⟨region.val - (1 + layout.proxyCount), by
        have hbound := region.isLt
        simp only [extractDiagramRaw, FragmentLayout.regionCount] at hbound
        omega⟩
    exact ⟨index, by
      apply Fin.ext
      simp [FragmentLayout.materialRegion, index]
      omega⟩
  · rintro ⟨index, rfl⟩
    change layout.materialRegion index ≠ layout.root ∧
      ∀ proxy, layout.materialRegion index ≠ layout.proxy proxy
    constructor
    · exact layout.materialRegion_ne_root index
    · intro proxy heq
      exact layout.proxy_ne_materialRegion proxy index heq.symm

private theorem fragmentParent_eq_bodyContainer_or_materialRegion
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (parent : Fin d.regionCount) :
    d.fragmentParent layout parent = layout.bodyContainer ∨
      ∃ index : Fin layout.materialRegionCount,
        d.fragmentParent layout parent = layout.materialRegion index := by
  unfold fragmentParent
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl

/-- Every copied node is owned by the terminal body or a material region. -/
theorem extractDiagramRaw_node_owner
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (node : Fin (d.extractDiagramRaw selection layout).nodeCount) :
    ((d.extractDiagramRaw selection layout).nodes node).region =
        layout.bodyContainer ∨
      ∃ index : Fin layout.materialRegionCount,
        ((d.extractDiagramRaw selection layout).nodes node).region =
          layout.materialRegion index := by
  change (d.fragmentNode selection layout node).region = layout.bodyContainer ∨
    ∃ index : Fin layout.materialRegionCount,
      (d.fragmentNode selection layout node).region = layout.materialRegion index
  unfold fragmentNode
  split <;> simpa only [CNode.region] using
    (d.fragmentParent_eq_bodyContainer_or_materialRegion selection layout _)

/-- Internal wires are owned by the terminal body or a material region. -/
theorem extractDiagramRaw_internalWire_scope
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (index : Fin layout.internalWireCount) :
    ((d.extractDiagramRaw selection layout).wires
        (layout.internalWire index)).scope = layout.bodyContainer ∨
      ∃ material : Fin layout.materialRegionCount,
        ((d.extractDiagramRaw selection layout).wires
          (layout.internalWire index)).scope = layout.materialRegion material := by
  simpa [extractDiagramRaw, fragmentWire, FragmentLayout.internalWire,
    fragmentInternalWire] using
    (d.fragmentParent_eq_bodyContainer_or_materialRegion selection layout
      (d.wires (selection.internalWires.get index)).scope)

/-- Every material region is attached beneath the terminal body or material. -/
theorem extractDiagramRaw_materialRegion_parent
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (index : Fin layout.materialRegionCount) :
    ((d.extractDiagramRaw selection layout).regions
        (layout.materialRegion index)).parent? = some layout.bodyContainer ∨
      ∃ parent : Fin layout.materialRegionCount,
        ((d.extractDiagramRaw selection layout).regions
          (layout.materialRegion index)).parent? =
            some (layout.materialRegion parent) := by
  rw [d.extractDiagramRaw_materialRegion selection layout index]
  change (d.fragmentMaterialRegion selection layout index).parent? =
      some layout.bodyContainer ∨
    ∃ parent : Fin layout.materialRegionCount,
      (d.fragmentMaterialRegion selection layout index).parent? =
        some (layout.materialRegion parent)
  unfold fragmentMaterialRegion
  cases hregion : d.regions (selection.selectedRegions.get index) with
  | sheet => exact Or.inl rfl
  | cut parent =>
      rcases d.fragmentParent_eq_bodyContainer_or_materialRegion
        selection layout parent with hbody | ⟨material, hmaterial⟩
      · exact Or.inl (congrArg some hbody)
      · exact Or.inr ⟨material, congrArg some hmaterial⟩
  | bubble parent arity =>
      rcases d.fragmentParent_eq_bodyContainer_or_materialRegion
        selection layout parent with hbody | ⟨material, hmaterial⟩
      · exact Or.inl (congrArg some hbody)
      · exact Or.inr ⟨material, congrArg some hmaterial⟩

/-- With proxies present, the first proxy is the sheet's sole direct child. -/
theorem extractDiagramRaw_root_direct_child
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (hnonzero : layout.proxyCount ≠ 0)
    (region : Fin (d.extractDiagramRaw selection layout).regionCount)
    (hparent : ((d.extractDiagramRaw selection layout).regions region).parent? =
      some layout.root) :
    region = layout.proxy ⟨0, by omega⟩ := by
  by_cases hroot : region = layout.root
  · subst region
    cases hparent
  by_cases hmaterial :
      (d.extractedBinderSpine selection layout).IsMaterialRegion region
  · obtain ⟨material, rfl⟩ :=
      (d.extractedBinderSpine_isMaterialRegion_iff selection layout _).1 hmaterial
    rcases d.extractDiagramRaw_materialRegion_parent selection layout material with
      hbody | ⟨parent, hparentMaterial⟩
    · rw [hbody] at hparent
      exact False.elim
        (layout.bodyContainer_ne_root_of_proxyCount_ne_zero hnonzero
          (Option.some.inj hparent))
    · rw [hparentMaterial] at hparent
      exact False.elim
        (layout.materialRegion_ne_root parent (Option.some.inj hparent))
  · have hproxy : ∃ index : Fin layout.proxyCount,
        region = layout.proxy index := by
      by_cases hexists : ∃ index : Fin layout.proxyCount,
          region = layout.proxy index
      · exact hexists
      · exfalso
        apply hmaterial
        exact ⟨by
          intro heq
          exact hroot (heq.trans rfl), by
          intro index heq
          exact hexists ⟨index, heq⟩⟩
    obtain ⟨index, rfl⟩ := hproxy
    rw [d.extractDiagramRaw_proxy_region selection layout index] at hparent
    simp only [CRegion.parent?] at hparent
    by_cases hzero : index.val = 0
    · apply congrArg layout.proxy
      apply Fin.ext
      simpa using hzero
    · have hbad : layout.proxy ⟨index.val - 1, by omega⟩ = layout.root := by
        simpa [proxyParent, hzero] using Option.some.inj hparent
      exact False.elim (layout.proxy_ne_root _ hbad)

/-- Each nonterminal proxy has the next proxy as its sole direct child. -/
theorem extractDiagramRaw_nonterminalProxy_direct_child
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (proxy : Fin layout.proxyCount)
    (hnonterminal : proxy.val + 1 < layout.proxyCount)
    (region : Fin (d.extractDiagramRaw selection layout).regionCount)
    (hparent : ((d.extractDiagramRaw selection layout).regions region).parent? =
      some (layout.proxy proxy)) :
    region = layout.proxy ⟨proxy.val + 1, hnonterminal⟩ := by
  by_cases hroot : region = layout.root
  · subst region
    cases hparent
  by_cases hmaterial :
      (d.extractedBinderSpine selection layout).IsMaterialRegion region
  · obtain ⟨material, rfl⟩ :=
      (d.extractedBinderSpine_isMaterialRegion_iff selection layout _).1 hmaterial
    rcases d.extractDiagramRaw_materialRegion_parent selection layout material with
      hbody | ⟨parent, hparentMaterial⟩
    · rw [hbody] at hparent
      exact False.elim
        (layout.bodyContainer_ne_nonterminalProxy proxy hnonterminal
          (Option.some.inj hparent))
    · rw [hparentMaterial] at hparent
      exact False.elim
        (layout.proxy_ne_materialRegion proxy parent
          (Option.some.inj hparent).symm)
  · have hproxy : ∃ index : Fin layout.proxyCount,
        region = layout.proxy index := by
      by_cases hexists : ∃ index : Fin layout.proxyCount,
          region = layout.proxy index
      · exact hexists
      · exfalso
        apply hmaterial
        exact ⟨by
          intro heq
          exact hroot (heq.trans rfl), by
          intro index heq
          exact hexists ⟨index, heq⟩⟩
    obtain ⟨index, rfl⟩ := hproxy
    rw [d.extractDiagramRaw_proxy_region selection layout index] at hparent
    simp only [CRegion.parent?] at hparent
    by_cases hzero : index.val = 0
    · have hbad : layout.root = layout.proxy proxy := by
        simpa [proxyParent, hzero] using Option.some.inj hparent
      exact False.elim (layout.proxy_ne_root proxy hbad.symm)
    · have hprevious :
          layout.proxy ⟨index.val - 1, by omega⟩ = layout.proxy proxy := by
        simpa [proxyParent, hzero] using Option.some.inj hparent
      have hindex : (⟨index.val - 1, by omega⟩ : Fin layout.proxyCount) =
          proxy := layout.proxy_injective hprevious
      have hvals : index.val - 1 = proxy.val := by
        simpa using congrArg Fin.val hindex
      have hfin : index = ⟨proxy.val + 1, hnonterminal⟩ := by
        apply Fin.ext
        have hone : 1 ≤ index.val := by omega
        calc
          index.val = index.val - 1 + 1 := (Nat.sub_add_cancel hone).symm
          _ = proxy.val + 1 := by rw [hvals]
      exact congrArg layout.proxy hfin

/-- A nonempty binder prefix leaves the fresh sheet free of material nodes. -/
theorem extractDiagramRaw_root_has_no_nodes_of_proxyCount_ne_zero
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (hnonzero : layout.proxyCount ≠ 0)
    (node : Fin (d.extractDiagramRaw selection layout).nodeCount) :
    ((d.extractDiagramRaw selection layout).nodes node).region ≠ layout.root := by
  intro hroot
  rcases d.extractDiagramRaw_node_owner selection layout node with
    hbody | ⟨material, hmaterial⟩
  · exact layout.bodyContainer_ne_root_of_proxyCount_ne_zero hnonzero
      (hbody.symm.trans hroot)
  · exact layout.materialRegion_ne_root material (hmaterial.symm.trans hroot)

/-- Nonterminal proxies own no material nodes; the terminal proxy owns the body. -/
theorem extractDiagramRaw_nonterminalProxy_has_no_nodes
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (proxy : Fin layout.proxyCount)
    (hnonterminal : proxy.val + 1 < layout.proxyCount)
    (node : Fin (d.extractDiagramRaw selection layout).nodeCount) :
    ((d.extractDiagramRaw selection layout).nodes node).region ≠
      layout.proxy proxy := by
  intro hproxy
  rcases d.extractDiagramRaw_node_owner selection layout node with
    hbody | ⟨material, hmaterial⟩
  · exact layout.bodyContainer_ne_nonterminalProxy proxy hnonterminal
      (hbody.symm.trans hproxy)
  · exact layout.proxy_ne_materialRegion proxy material
      (hproxy.symm.trans hmaterial)

/-- A nonempty binder prefix leaves the fresh sheet free of internal wires. -/
theorem extractDiagramRaw_root_has_no_internalWires_of_proxyCount_ne_zero
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (hnonzero : layout.proxyCount ≠ 0)
    (wire : Fin layout.internalWireCount) :
    ((d.extractDiagramRaw selection layout).wires
      (layout.internalWire wire)).scope ≠ layout.root := by
  intro hroot
  rcases d.extractDiagramRaw_internalWire_scope selection layout wire with
    hbody | ⟨material, hmaterial⟩
  · exact layout.bodyContainer_ne_root_of_proxyCount_ne_zero hnonzero
      (hbody.symm.trans hroot)
  · exact layout.materialRegion_ne_root material (hmaterial.symm.trans hroot)

/-- Nonterminal proxies own no internal wires. -/
theorem extractDiagramRaw_nonterminalProxy_has_no_internalWires
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (proxy : Fin layout.proxyCount)
    (hnonterminal : proxy.val + 1 < layout.proxyCount)
    (wire : Fin layout.internalWireCount) :
    ((d.extractDiagramRaw selection layout).wires
      (layout.internalWire wire)).scope ≠ layout.proxy proxy := by
  intro hproxy
  rcases d.extractDiagramRaw_internalWire_scope selection layout wire with
    hbody | ⟨material, hmaterial⟩
  · exact layout.bodyContainer_ne_nonterminalProxy proxy hnonterminal
      (hbody.symm.trans hproxy)
  · exact layout.proxy_ne_materialRegion proxy material
      (hproxy.symm.trans hmaterial)

/-- With proxies present, every nonboundary sheet wire would have to be internal. -/
theorem extractDiagramRaw_root_has_no_nonboundaryWires_of_proxyCount_ne_zero
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (hnonzero : layout.proxyCount ≠ 0)
    (wire : Fin (d.extractDiagramRaw selection layout).wireCount)
    (hnotBoundary : wire ∉ d.extractBoundaryRaw selection layout) :
    ((d.extractDiagramRaw selection layout).wires wire).scope ≠ layout.root := by
  revert hnotBoundary
  refine Fin.addCases (fun internal _ => ?_) (fun boundary hnotBoundary => ?_) wire
  · exact d.extractDiagramRaw_root_has_no_internalWires_of_proxyCount_ne_zero
      selection layout hnonzero internal
  · exfalso
    apply hnotBoundary
    exact List.mem_ofFn.mpr ⟨boundary, rfl⟩

/-- Every nonboundary wire also avoids each nonterminal proxy. -/
theorem extractDiagramRaw_nonterminalProxy_has_no_nonboundaryWires
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (proxy : Fin layout.proxyCount)
    (hnonterminal : proxy.val + 1 < layout.proxyCount)
    (wire : Fin (d.extractDiagramRaw selection layout).wireCount)
    (hnotBoundary : wire ∉ d.extractBoundaryRaw selection layout) :
    ((d.extractDiagramRaw selection layout).wires wire).scope ≠
      layout.proxy proxy := by
  revert hnotBoundary
  refine Fin.addCases (fun internal _ => ?_) (fun boundary hnotBoundary => ?_) wire
  · exact d.extractDiagramRaw_nonterminalProxy_has_no_internalWires
      selection layout proxy hnonterminal internal
  · exfalso
    apply hnotBoundary
    exact List.mem_ofFn.mpr ⟨boundary, rfl⟩

/-- Every generated proxy arity is copied from its aligned external host binder. -/
theorem extractedBinderSpine_target_region
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (index : Fin layout.proxyCount) :
    ∃ parent,
      host.val.regions (layout.externalBinders.get index) =
        .bubble parent
          ((host.val.extractedBinderSpine selection layout).arity index) := by
  have hmemberLayout : layout.externalBinders.get index ∈
      layout.externalBinders := List.get_mem _ _
  have hmemberSelection : layout.externalBinders.get index ∈
      selection.externalBinders := by
    rw [← layout.externalBinders_exact]
    exact hmemberLayout
  obtain ⟨_, node, _, hatom⟩ :=
    selection.mem_externalBinders_uses hmemberSelection
  cases hnode : host.val.nodes node with
  | term region freePorts term =>
      simp [hnode] at hatom
  | named region definition arity =>
      simp [hnode] at hatom
  | atom region binder =>
      simp only [hnode] at hatom
      subst binder
      have hbubble := host.property.atom_binders_are_bubbles node
      simp only [hnode] at hbubble
      obtain ⟨parent, arity, hregion⟩ := hbubble
      have hbinderArity :
          host.val.binderArity? (layout.externalBinders.get index) =
            some arity := by
        unfold ConcreteDiagram.binderArity?
        rw [hregion]
      have harity :
          (host.val.extractedBinderSpine selection layout).arity index =
            arity := by
        change (host.val.binderArity? (layout.externalBinders.get index)).getD 0 =
          arity
        rw [hbinderArity]
        rfl
      refine ⟨parent, ?_⟩
      rw [harity]
      exact hregion

@[simp] theorem extractBoundaryRaw_length (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection) :
    (d.extractBoundaryRaw selection layout).length =
      selection.touchingWires.length := by
  simp [extractBoundaryRaw, FragmentLayout.boundaryWireCount]

theorem extractBoundaryRaw_root_scoped (d : ConcreteDiagram)
    (selection : CheckedSelection d) (layout : FragmentLayout d selection) :
    ∀ wire, wire ∈ d.extractBoundaryRaw selection layout →
      ((d.extractDiagramRaw selection layout).wires wire).scope =
        (d.extractDiagramRaw selection layout).root := by
  intro wire hwire
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hwire
  simp [extractDiagramRaw, fragmentWire, FragmentLayout.boundaryWire,
    fragmentBoundaryWire]

/-- Extraction satisfies the complete terminal-body prefix contract. -/
theorem extractedBinderSpine_terminalBodyContract
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) :
    (d.extractedBinderSpine selection layout).TerminalBodyContract
      (d.extractOpenRaw selection layout) where
  root_direct_child := by
    intro hnonzero region hparent
    exact d.extractDiagramRaw_root_direct_child selection layout hnonzero
      region hparent
  nonterminal_direct_child := by
    intro proxy hnonterminal region hparent
    exact d.extractDiagramRaw_nonterminalProxy_direct_child selection layout
      proxy hnonterminal region hparent
  root_has_no_nodes := by
    intro hnonzero node
    exact d.extractDiagramRaw_root_has_no_nodes_of_proxyCount_ne_zero
      selection layout hnonzero node
  nonterminal_has_no_nodes := by
    intro proxy hnonterminal node
    exact d.extractDiagramRaw_nonterminalProxy_has_no_nodes selection layout
      proxy hnonterminal node
  root_has_no_nonboundary_wires := by
    intro hnonzero wire hnotBoundary
    exact d.extractDiagramRaw_root_has_no_nonboundaryWires_of_proxyCount_ne_zero
      selection layout hnonzero wire hnotBoundary
  nonterminal_has_no_nonboundary_wires := by
    intro proxy hnonterminal wire hnotBoundary
    exact d.extractDiagramRaw_nonterminalProxy_has_no_nonboundaryWires
      selection layout proxy hnonterminal wire hnotBoundary
  boundary_is_root_scoped := by
    exact d.extractBoundaryRaw_root_scoped selection layout

end ConcreteDiagram

/-- Proof-free decomposition projection produced before graph validation. -/
structure RawExtraction (host : ConcreteDiagram)
    (selection : CheckedSelection host) where
  layout : FragmentLayout host selection := {}
  fragment : OpenConcreteDiagram := host.extractOpenRaw selection layout
  fragment_exact : fragment = host.extractOpenRaw selection layout := by rfl
  attachments : List (Fin host.wireCount) := selection.touchingWires
  attachments_exact : attachments = selection.touchingWires := by rfl

/-- A successfully validated extraction with its administrative interface data. -/
structure CheckedExtraction (signature : List Nat) (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) where
  raw : RawExtraction host.val selection
  fragment : CheckedOpenDiagram signature
  fragment_eq : fragment.val = raw.fragment

namespace RawExtraction

def check {signature : List Nat} {host : CheckedDiagram signature}
    {selection : CheckedSelection host.val}
    (raw : RawExtraction host.val selection) :
    Except WFError (CheckedExtraction signature host selection) :=
  match hcheck : checkWellFormed signature raw.fragment.diagram with
  | .error error => .error error
  | .ok checked =>
      .ok {
        raw
        fragment := ⟨raw.fragment, {
          diagram_well_formed := by
            have hinput := checkWellFormed_preserves_input hcheck
            rw [← hinput]
            exact checked.property
          boundary_is_root_scoped := by
            rw [raw.fragment_exact]
            exact host.val.extractBoundaryRaw_root_scoped selection raw.layout
        }⟩
        fragment_eq := rfl
      }

end RawExtraction

/-- Compute extraction and validate it through the sole concrete validator. -/
def extractChecked (signature : List Nat) (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) :
    Except WFError (CheckedExtraction signature host selection) :=
  RawExtraction.check ({} : RawExtraction host.val selection)

theorem extractChecked_sound
    (_h : extractChecked signature host selection = .ok extraction) :
    extraction.fragment.val.WellFormed signature :=
  extraction.fragment.property

end VisualProof.Diagram
