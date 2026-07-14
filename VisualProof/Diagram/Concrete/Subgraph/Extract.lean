import VisualProof.Diagram.Concrete.Subgraph.Selection
import VisualProof.Diagram.Concrete.WellFormed
import VisualProof.Diagram.Concrete.Open
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

private theorem selectsRegion_downward {d : ConcreteDiagram}
    (hwf : d.WellFormed signature) {request : SelectionRequest d}
    {ancestor descendant : Fin d.regionCount}
    (hselected : request.SelectsRegion ancestor)
    (hencloses : d.Encloses ancestor descendant) :
    request.SelectsRegion descendant := by
  obtain ⟨root, hroot, hrootAncestor⟩ := hselected
  exact ⟨root, hroot,
    ConcreteElaboration.checked_encloses_trans hwf hrootAncestor hencloses⟩

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

private def fragmentWireOrigin (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) :
    Fin layout.wireCount → Fin d.wireCount :=
  Fin.addCases selection.internalWires.get selection.touchingWires.get

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

@[simp] theorem extractDiagramRaw_node
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (index : Fin layout.nodeCount) :
    (d.extractDiagramRaw selection layout).nodes index =
      d.fragmentNode selection layout index := rfl

theorem extractDiagramRaw_node_region
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (index : Fin layout.nodeCount) :
    ((d.extractDiagramRaw selection layout).nodes index).region =
      d.fragmentParent layout
        (d.nodes (selection.selectedNodes.get index)).region := by
  rw [d.extractDiagramRaw_node selection layout index]
  unfold fragmentNode
  split <;> rename_i hnode <;> rw [hnode] <;> rfl

theorem extractDiagramRaw_atom_binder_bubble
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (index : Fin layout.nodeCount)
    {region binder : Fin host.val.regionCount}
    (hnode : host.val.nodes (selection.selectedNodes.get index) =
      .atom region binder) :
    ∃ hostParent extractedParent arity,
      host.val.regions binder = .bubble hostParent arity ∧
      (host.val.extractDiagramRaw selection layout).regions
          (host.val.fragmentBinder layout binder) =
        .bubble extractedParent arity := by
  have hbubble := host.property.atom_binders_are_bubbles
    (selection.selectedNodes.get index)
  simp only [hnode] at hbubble
  obtain ⟨hostParent, arity, hkind⟩ := hbubble
  by_cases hselected : binder ∈ selection.selectedRegions
  · obtain ⟨found, hfound⟩ := indexOf?_complete hselected
    have hget : selection.selectedRegions.get found = binder :=
      indexOf?_sound hfound
    refine ⟨hostParent, host.val.fragmentParent layout hostParent, arity,
      hkind, ?_⟩
    unfold fragmentBinder
    rw [hfound]
    rw [host.val.extractDiagramRaw_materialRegion selection layout found]
    unfold fragmentMaterialRegion
    rw [hget, hkind]
    rfl
  · have huses : selection.UsesExternalBinder binder :=
      ⟨hselected, selection.selectedNodes.get index, List.get_mem _ _, by
        simp only [hnode]⟩
    have hexternal : binder ∈ selection.externalBinders :=
      (selection.mem_externalBinders_iff_uses host binder).2 huses
    have hlayout : binder ∈ layout.externalBinders := by
      rw [layout.externalBinders_exact]
      exact hexternal
    obtain ⟨found, hfound⟩ := indexOf?_complete hlayout
    have hget : layout.externalBinders.get found = binder :=
      indexOf?_sound hfound
    refine ⟨hostParent, proxyParent layout found, arity, hkind, ?_⟩
    unfold fragmentBinder
    have hselectedNone : indexOf? selection.selectedRegions binder = none := by
      cases hfoundSelected : indexOf? selection.selectedRegions binder with
      | none => rfl
      | some selectedIndex =>
          exfalso
          apply hselected
          rw [← indexOf?_sound hfoundSelected]
          exact List.get_mem _ _
    rw [hselectedNone, hfound]
    rw [host.val.extractDiagramRaw_proxy_region selection layout found]
    unfold proxyArity ConcreteDiagram.binderArity?
    rw [hget, hkind]
    rfl

theorem extractDiagramRaw_requiresPort_iff
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (node : Fin layout.nodeCount) (port : CPort) :
    (host.val.extractDiagramRaw selection layout).RequiresPort node port ↔
      host.val.RequiresPort (selection.selectedNodes.get node) port := by
  cases hnode : host.val.nodes (selection.selectedNodes.get node) with
  | term region freePorts term =>
      unfold ConcreteDiagram.RequiresPort
      simp only [extractDiagramRaw_node, fragmentNode, hnode]
  | named region definition arity =>
      unfold ConcreteDiagram.RequiresPort
      simp only [extractDiagramRaw_node, fragmentNode, hnode]
  | atom region binder =>
      obtain ⟨hostParent, extractedParent, arity, hhost, hextracted⟩ :=
        extractDiagramRaw_atom_binder_bubble host selection layout node hnode
      unfold ConcreteDiagram.RequiresPort
      simp only [extractDiagramRaw_node, fragmentNode, hnode]
      rw [hextracted, hhost]

theorem fragmentEndpoint?_origin
    (selection : CheckedSelection d)
    {original : CEndpoint d.nodeCount}
    {mapped : CEndpoint selection.selectedNodes.length}
    (hmapped : fragmentEndpoint? selection original = some mapped) :
    original = {
      node := selection.selectedNodes.get mapped.node
      port := mapped.port
    } := by
  unfold fragmentEndpoint? at hmapped
  cases hindex : indexOf? selection.selectedNodes original.node with
  | none => simp [hindex] at hmapped
  | some node =>
      simp only [hindex, Option.map_some] at hmapped
      cases hmapped
      have hnode := indexOf?_sound hindex
      cases original
      simp only at hnode
      cases hnode
      rfl

theorem fragmentEndpoint?_some_injective
    (selection : CheckedSelection d)
    {first second : CEndpoint d.nodeCount}
    {mapped : CEndpoint selection.selectedNodes.length}
    (hfirst : fragmentEndpoint? selection first = some mapped)
    (hsecond : fragmentEndpoint? selection second = some mapped) :
    first = second := by
  rw [fragmentEndpoint?_origin selection hfirst,
    fragmentEndpoint?_origin selection hsecond]

@[simp] theorem extractDiagramRaw_wire_endpoints
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (wire : Fin layout.wireCount) :
    ((d.extractDiagramRaw selection layout).wires wire).endpoints =
      (d.wires (fragmentWireOrigin selection layout wire)).endpoints.filterMap
        (fragmentEndpoint? selection) := by
  revert wire
  apply Fin.addCases
  · intro internal
    simp [extractDiagramRaw, fragmentWire, fragmentInternalWire,
      fragmentEndpoints, fragmentWireOrigin]
  · intro boundary
    simp [extractDiagramRaw, fragmentWire, fragmentBoundaryWire,
      fragmentEndpoints, fragmentWireOrigin]

theorem mem_extractDiagramRaw_wire_endpoints_iff
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (wire : Fin layout.wireCount)
    (endpoint : CEndpoint layout.nodeCount) :
    endpoint ∈ ((d.extractDiagramRaw selection layout).wires wire).endpoints ↔
      ∃ original,
        original ∈
          (d.wires (fragmentWireOrigin selection layout wire)).endpoints ∧
        fragmentEndpoint? selection original = some endpoint := by
  rw [d.extractDiagramRaw_wire_endpoints selection layout wire]
  exact List.mem_filterMap

theorem fragmentWireOrigin_injective
    (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) :
    Function.Injective (fragmentWireOrigin selection layout) := by
  intro first
  revert first
  apply Fin.addCases
  · intro left second heq
    revert second
    apply Fin.addCases
    · intro right heq
      have hindex : left = right := by
        apply Fin.ext
        exact (List.getElem_inj selection.internalWires_nodup).mp (by
          simpa [fragmentWireOrigin] using heq)
      exact congrArg (Fin.castAdd layout.boundaryWireCount) hindex
    · intro right heq
      exfalso
      have horigin : selection.internalWires.get left =
          selection.touchingWires.get right := by
        simpa [fragmentWireOrigin] using heq
      exact selection.internalWires_touchingWires_disjoint
        (selection.internalWires.get left) (List.get_mem _ _) (by
          rw [horigin]
          exact List.get_mem _ _)
  · intro left second heq
    revert second
    apply Fin.addCases
    · intro right heq
      exfalso
      have horigin : selection.touchingWires.get left =
          selection.internalWires.get right := by
        simpa [fragmentWireOrigin] using heq
      exact selection.internalWires_touchingWires_disjoint
        (selection.internalWires.get right) (List.get_mem _ _) (by
          rw [← horigin]
          exact List.get_mem _ _)
    · intro right heq
      have hindex : left = right := by
        apply Fin.ext
        exact (List.getElem_inj selection.touchingWires_nodup).mp (by
          simpa [fragmentWireOrigin] using heq)
      exact congrArg (Fin.natAdd layout.internalWireCount) hindex

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

theorem extractDiagramRaw_endpoints_are_nodup
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).EndpointsAreNodup := by
  intro wire
  rw [host.val.extractDiagramRaw_wire_endpoints selection layout wire]
  exact filterMap_nodup_of_some_injective
    (host.property.endpoints_are_nodup
      (fragmentWireOrigin selection layout wire))
    (fun hfirst hsecond =>
      fragmentEndpoint?_some_injective selection hfirst hsecond)

theorem extractDiagramRaw_wire_endpoints_are_disjoint
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).WireEndpointsAreDisjoint := by
  intro first second hne endpoint hfirst
  rw [Bool.not_eq_true', decide_eq_false_iff_not]
  intro hsecond
  obtain ⟨firstOriginal, hfirstMember, hfirstMapped⟩ :=
    (host.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
      first endpoint).1 hfirst
  obtain ⟨secondOriginal, hsecondMember, hsecondMapped⟩ :=
    (host.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
      second endpoint).1 hsecond
  have hsame := fragmentEndpoint?_some_injective selection
    hfirstMapped hsecondMapped
  subst secondOriginal
  have hneProp : first ≠ second := by simpa using hne
  have horiginNe : fragmentWireOrigin selection layout first ≠
      fragmentWireOrigin selection layout second := by
    intro heq
    exact hneProp (fragmentWireOrigin_injective selection layout heq)
  have horiginNeBool :
      (fragmentWireOrigin selection layout first !=
        fragmentWireOrigin selection layout second) = true := by
    simpa using horiginNe
  have hdisjoint := host.property.wire_endpoints_are_disjoint
    (fragmentWireOrigin selection layout first)
    (fragmentWireOrigin selection layout second) horiginNeBool
    firstOriginal hfirstMember
  rw [Bool.not_eq_true', decide_eq_false_iff_not] at hdisjoint
  exact hdisjoint hsecondMember

theorem extractDiagramRaw_endpoints_are_valid
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).EndpointsAreValid := by
  intro wire endpoint hendpoint
  obtain ⟨original, horiginal, hmapped⟩ :=
    (host.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
      wire endpoint).1 hendpoint
  have hvalid := host.property.endpoints_are_valid
    (fragmentWireOrigin selection layout wire) original horiginal
  have horigin := fragmentEndpoint?_origin selection hmapped
  rw [horigin] at hvalid
  exact (extractDiagramRaw_requiresPort_iff host selection layout
    endpoint.node endpoint.port).2 hvalid

theorem extractDiagramRaw_endpointOccurs_of_selected
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    {wire : Fin host.val.wireCount} (node : Fin layout.nodeCount)
    (port : CPort)
    (hoccurs : host.val.EndpointOccurs wire {
      node := selection.selectedNodes.get node
      port := port
    }) :
    ∃ mappedWire,
      (host.val.extractDiagramRaw selection layout).EndpointOccurs mappedWire
        { node := node, port := port } := by
  let original : CEndpoint host.val.nodeCount := {
    node := selection.selectedNodes.get node
    port := port
  }
  have hmapped : fragmentEndpoint? selection original =
      some ({ node := node, port := port } : CEndpoint layout.nodeCount) := by
    unfold fragmentEndpoint? original
    rw [indexOf?_get_eq_some_of_nodup selection.selectedNodes_nodup]
    rfl
  by_cases hinternal : wire ∈ selection.internalWires
  · obtain ⟨index, hindex⟩ := indexOf?_complete hinternal
    refine ⟨layout.internalWire index, ?_⟩
    apply (host.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
      (layout.internalWire index) _).2
    refine ⟨original, ?_, hmapped⟩
    change original ∈
      (host.val.wires (fragmentWireOrigin selection layout
        (layout.internalWire index))).endpoints
    simp only [fragmentWireOrigin, FragmentLayout.internalWire,
      Fin.addCases_left]
    have hget : selection.internalWires.get index = wire :=
      indexOf?_sound hindex
    rw [hget]
    simpa only [ConcreteDiagram.EndpointOccurs, original] using hoccurs
  · have htouching : wire ∈ selection.touchingWires :=
      selection.noninternal_with_selectedEndpoint_mem_touching hinternal
        ⟨original, hoccurs, List.get_mem _ _⟩
    obtain ⟨index, hindex⟩ := indexOf?_complete htouching
    refine ⟨layout.boundaryWire index, ?_⟩
    apply (host.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
      (layout.boundaryWire index) _).2
    refine ⟨original, ?_, hmapped⟩
    change original ∈
      (host.val.wires (fragmentWireOrigin selection layout
        (layout.boundaryWire index))).endpoints
    simp only [fragmentWireOrigin, FragmentLayout.boundaryWire,
      Fin.addCases_right]
    have hget : selection.touchingWires.get index = wire :=
      indexOf?_sound hindex
    rw [hget]
    simpa only [ConcreteDiagram.EndpointOccurs, original] using hoccurs

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

theorem extractDiagramRaw_region_cases
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (region : Fin (d.extractDiagramRaw selection layout).regionCount) :
    region = layout.root ∨
      (∃ index : Fin layout.proxyCount, region = layout.proxy index) ∨
      ∃ index : Fin layout.materialRegionCount,
        region = layout.materialRegion index := by
  by_cases hroot : region = layout.root
  · exact Or.inl hroot
  by_cases hmaterial :
      (d.extractedBinderSpine selection layout).IsMaterialRegion region
  · exact Or.inr (Or.inr
      ((d.extractedBinderSpine_isMaterialRegion_iff selection layout region).1
        hmaterial |>.imp fun _ heq => heq.symm))
  · right
    left
    by_cases hproxy : ∃ index : Fin layout.proxyCount,
        region = layout.proxy index
    · exact hproxy
    · exact False.elim (hmaterial ⟨hroot, by
        intro index heq
        exact hproxy ⟨index, heq⟩⟩)

private theorem selectedRegion_ne_root
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    {region : Fin host.val.regionCount}
    (hselected : region ∈ selection.selectedRegions) :
    region ≠ host.val.root := by
  intro heq
  obtain ⟨child, hchild, hencloses⟩ :=
    (selection.mem_selectedRegions region).1 hselected
  rw [heq] at hencloses
  have hchildRoot := ConcreteElaboration.encloses_sheet_eq
    host.property.root_is_sheet hencloses
  have hparent := selection.property.childRoots_direct child hchild
  rw [hchildRoot, host.property.root_is_sheet] at hparent
  contradiction

private theorem anchor_not_mem_selectedRegions
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) :
    selection.val.anchor ∉ selection.selectedRegions := by
  intro hselected
  obtain ⟨child, hchild, hencloses⟩ :=
    (selection.mem_selectedRegions selection.val.anchor).1 hselected
  exact ConcreteElaboration.checked_direct_child_not_encloses_parent
    host.property (selection.property.childRoots_direct child hchild) hencloses

theorem fragmentParent_anchor
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) :
    d.fragmentParent layout selection.val.anchor = layout.bodyContainer := by
  simp [fragmentParent]

theorem fragmentParent_selectedRegion
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    {region : Fin host.val.regionCount}
    (hselected : region ∈ selection.selectedRegions) :
    ∃ index : Fin layout.materialRegionCount,
      selection.selectedRegions.get index = region ∧
      host.val.fragmentParent layout region = layout.materialRegion index := by
  obtain ⟨index, hindex⟩ := indexOf?_complete hselected
  refine ⟨index, indexOf?_sound hindex, ?_⟩
  unfold fragmentParent
  have hneAnchor : region ≠ selection.val.anchor := by
    intro heq
    subst region
    exact anchor_not_mem_selectedRegions host selection hselected
  simp [hneAnchor, hindex]

theorem extractDiagramRaw_materialRegion_parent_exact
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (index : Fin layout.materialRegionCount)
    {parent : Fin host.val.regionCount}
    (hparent : (host.val.regions
      (selection.selectedRegions.get index)).parent? = some parent) :
    ((host.val.extractDiagramRaw selection layout).regions
      (layout.materialRegion index)).parent? =
        some (host.val.fragmentParent layout parent) := by
  rw [host.val.extractDiagramRaw_materialRegion selection layout index]
  unfold fragmentMaterialRegion
  split
  · rename_i hkind
    rw [hkind] at hparent
    contradiction
  · rename_i candidate hkind
    rw [hkind] at hparent
    have heq : candidate = parent := Option.some.inj hparent
    subst candidate
    rfl
  · rename_i candidate arity hkind
    rw [hkind] at hparent
    have heq : candidate = parent := Option.some.inj hparent
    subst candidate
    rfl

theorem extractDiagramRaw_climb_selected
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    {finish : Fin host.val.regionCount}
    (hfinish : finish ∈ selection.selectedRegions)
    (index : Fin layout.materialRegionCount)
    (steps : Nat) (hbound : steps < host.val.regionCount + 1)
    (hclimb : host.val.climb steps
      (selection.selectedRegions.get index) = some finish) :
    ∃ finishIndex : Fin layout.materialRegionCount,
      selection.selectedRegions.get finishIndex = finish ∧
      (host.val.extractDiagramRaw selection layout).climb steps
          (layout.materialRegion index) =
        some (layout.materialRegion finishIndex) := by
  induction steps generalizing index with
  | zero =>
      have heq := Option.some.inj hclimb
      exact ⟨index, heq, rfl⟩
  | succ steps ih =>
      cases hkind : host.val.regions (selection.selectedRegions.get index) with
      | sheet =>
          have hroot := host.property.only_root_is_sheet
            (selection.selectedRegions.get index) hkind
          exact False.elim
            (selectedRegion_ne_root host selection (List.get_mem _ _) hroot)
      | cut parent =>
          have hparent :
              (host.val.regions
                (selection.selectedRegions.get index)).parent? = some parent :=
            (congrArg CRegion.parent? hkind).trans rfl
          have htail : host.val.climb steps parent = some finish := by
            simpa only [ConcreteDiagram.climb, hparent] using hclimb
          have hselectedParent : parent ∈ selection.selectedRegions :=
            (selection.mem_selectedRegions parent).2
              (selectsRegion_downward host.property
                ((selection.mem_selectedRegions finish).1 hfinish)
                ⟨⟨steps, by omega⟩, htail⟩)
          obtain ⟨parentIndex, hget, hfragment⟩ :=
            fragmentParent_selectedRegion host selection layout hselectedParent
          obtain ⟨finishIndex, hfinishGet, hfragmentClimb⟩ :=
            ih parentIndex (by omega) (by rw [hget]; exact htail)
          refine ⟨finishIndex, hfinishGet, ?_⟩
          simp only [ConcreteDiagram.climb]
          rw [extractDiagramRaw_materialRegion_parent_exact host
            selection layout index hparent]
          rw [hfragment]
          exact hfragmentClimb
      | bubble parent arity =>
          have hparent :
              (host.val.regions
                (selection.selectedRegions.get index)).parent? = some parent :=
            (congrArg CRegion.parent? hkind).trans rfl
          have htail : host.val.climb steps parent = some finish := by
            simpa only [ConcreteDiagram.climb, hparent] using hclimb
          have hselectedParent : parent ∈ selection.selectedRegions :=
            (selection.mem_selectedRegions parent).2
              (selectsRegion_downward host.property
                ((selection.mem_selectedRegions finish).1 hfinish)
                ⟨⟨steps, by omega⟩, htail⟩)
          obtain ⟨parentIndex, hget, hfragment⟩ :=
            fragmentParent_selectedRegion host selection layout hselectedParent
          obtain ⟨finishIndex, hfinishGet, hfragmentClimb⟩ :=
            ih parentIndex (by omega) (by rw [hget]; exact htail)
          refine ⟨finishIndex, hfinishGet, ?_⟩
          simp only [ConcreteDiagram.climb]
          rw [extractDiagramRaw_materialRegion_parent_exact host
            selection layout index hparent]
          rw [hfragment]
          exact hfragmentClimb

theorem extractDiagramRaw_climb_selected_steps_lt_materialRegionCount
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    {finish : Fin host.val.regionCount}
    (hfinish : finish ∈ selection.selectedRegions)
    (index : Fin layout.materialRegionCount)
    (steps : Nat) (hbound : steps < host.val.regionCount + 1)
    (hclimb : host.val.climb steps
      (selection.selectedRegions.get index) = some finish) :
    steps < layout.materialRegionCount := by
  let start := selection.selectedRegions.get index
  let pathIsSome (position : Fin (steps + 1)) :
      (host.val.climb position.val start).isSome = true :=
    Option.isSome_iff_exists.mpr
      (climb_prefix_exists (Nat.le_of_lt_succ position.isLt) hclimb)
  let path (position : Fin (steps + 1)) : Fin host.val.regionCount :=
    (host.val.climb position.val start).get (pathIsSome position)
  have path_spec (position : Fin (steps + 1)) :
      host.val.climb position.val start = some (path position) :=
    (Option.some_get (pathIsSome position)).symm
  have path_selected (position : Fin (steps + 1)) :
      path position ∈ selection.selectedRegions := by
    apply (selection.mem_selectedRegions (path position)).2
    exact selectsRegion_downward host.property
      ((selection.mem_selectedRegions finish).1 hfinish)
      ⟨⟨steps - position.val, by omega⟩,
        climb_cancel_prefix (Nat.le_of_lt_succ position.isLt)
          (path_spec position) hclimb⟩
  let pathIndex (position : Fin (steps + 1)) :
      Fin selection.selectedRegions.length :=
    (indexOf? selection.selectedRegions (path position)).get
      ((indexOf?_isSome_iff).2 (path_selected position))
  have pathIndex_spec (position : Fin (steps + 1)) :
      selection.selectedRegions.get (pathIndex position) = path position := by
    let hsome : (indexOf? selection.selectedRegions
        (path position)).isSome = true :=
      (indexOf?_isSome_iff).2 (path_selected position)
    obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
    have hindex : pathIndex position = found := by
      unfold pathIndex
      exact Option.get_of_eq_some hsome hfound
    rw [hindex]
    exact indexOf?_sound hfound
  have pathIndex_injective : Function.Injective pathIndex := by
    intro first second heq
    have hpaths : path first = path second := by
      rw [← pathIndex_spec first, ← pathIndex_spec second, heq]
    obtain ⟨finishRootSteps, hfinishRoot⟩ :=
      host.property.all_regions_reach_root finish
    have hfirstSuffix := climb_cancel_prefix
      (Nat.le_of_lt_succ first.isLt) (path_spec first) hclimb
    have hsecondSuffix := climb_cancel_prefix
      (Nat.le_of_lt_succ second.isLt) (path_spec second) hclimb
    have hfirstRoot := ConcreteElaboration.climb_add hfirstSuffix hfinishRoot
    have hsecondRoot := ConcreteElaboration.climb_add hsecondSuffix hfinishRoot
    rw [hpaths] at hfirstRoot
    have hremaining :=
      ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique host.val
        host.property.root_is_sheet hfirstRoot hsecondRoot
    apply Fin.ext
    omega
  have hcard := fin_card_le_of_injective pathIndex pathIndex_injective
  simpa only [FragmentLayout.materialRegionCount] using (show
    steps < selection.selectedRegions.length by omega)

private theorem extractDiagramRaw_proxy_climb_aux
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (value : Nat) :
    ∀ index : Fin layout.proxyCount, index.val = value →
      (d.extractDiagramRaw selection layout).climb (value + 1)
          (layout.proxy index) = some layout.root := by
  induction value with
  | zero =>
      intro index hvalue
      simp only [ConcreteDiagram.climb]
      rw [d.extractDiagramRaw_proxy_region selection layout index]
      simp [CRegion.parent?, proxyParent, hvalue]
      rfl
  | succ value ih =>
      intro index hvalue
      let previous : Fin layout.proxyCount := ⟨index.val - 1, by omega⟩
      have hindexPositive : index.val ≠ 0 := by omega
      have hparent :
          ((d.extractDiagramRaw selection layout).regions
            (layout.proxy index)).parent? = some (layout.proxy previous) := by
        rw [d.extractDiagramRaw_proxy_region selection layout index]
        simp only [CRegion.parent?]
        simp [proxyParent, hindexPositive, previous]
        rfl
      have hpreviousValue : previous.val = value := by
        simp [previous]
        omega
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
        ConcreteDiagram.climb, hparent] using ih previous hpreviousValue

theorem extractDiagramRaw_proxy_climb
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (index : Fin layout.proxyCount) :
    (d.extractDiagramRaw selection layout).climb (index.val + 1)
        (layout.proxy index) = some layout.root := by
  exact extractDiagramRaw_proxy_climb_aux d selection layout index.val index rfl

private theorem extractDiagramRaw_proxy_climb_between_aux
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) (value : Nat) :
    ∀ source target : Fin layout.proxyCount, source.val = value →
      target.val ≤ source.val →
      (d.extractDiagramRaw selection layout).climb
          (source.val - target.val) (layout.proxy source) =
        some (layout.proxy target) := by
  induction value with
  | zero =>
      intro source target hsource hle
      have heq : source = target := by
        apply Fin.ext
        omega
      subst target
      simp
      rfl
  | succ value ih =>
      intro source target hsource hle
      by_cases hequal : target.val = source.val
      · have heq : target = source := Fin.ext hequal
        subst target
        simp
        rfl
      · let previous : Fin layout.proxyCount := ⟨source.val - 1, by omega⟩
        have hsourcePositive : source.val ≠ 0 := by omega
        have hpreviousValue : previous.val = value := by
          simp [previous]
          omega
        have htargetPrevious : target.val ≤ previous.val := by
          simp [previous]
          omega
        have hparent :
            ((d.extractDiagramRaw selection layout).regions
              (layout.proxy source)).parent? = some (layout.proxy previous) := by
          rw [d.extractDiagramRaw_proxy_region selection layout source]
          simp only [CRegion.parent?]
          simp [proxyParent, hsourcePositive, previous]
          rfl
        have hsteps : source.val - target.val =
            (previous.val - target.val) + 1 := by
          simp [previous]
          omega
        rw [hsteps]
        simp only [ConcreteDiagram.climb, hparent]
        exact ih previous target hpreviousValue htargetPrevious

theorem extractDiagramRaw_proxy_climb_between
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (source target : Fin layout.proxyCount) (hle : target.val ≤ source.val) :
    (d.extractDiagramRaw selection layout).climb
        (source.val - target.val) (layout.proxy source) =
      some (layout.proxy target) := by
  exact extractDiagramRaw_proxy_climb_between_aux d selection layout
    source.val source target rfl hle

theorem extractDiagramRaw_proxy_encloses_bodyContainer
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection)
    (proxy : Fin layout.proxyCount) :
    (d.extractDiagramRaw selection layout).Encloses
      (layout.proxy proxy) layout.bodyContainer := by
  have hnonzero : layout.proxyCount ≠ 0 := by
    have := proxy.isLt
    omega
  let terminal : Fin layout.proxyCount :=
    ⟨layout.proxyCount - 1, by omega⟩
  have hbody : layout.bodyContainer = layout.proxy terminal :=
    layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hnonzero
  have hle : proxy.val ≤ terminal.val := by
    simp [terminal]
    omega
  refine ⟨⟨terminal.val - proxy.val, by
    simp only [extractDiagramRaw, FragmentLayout.regionCount]
    omega⟩, ?_⟩
  rw [hbody]
  exact d.extractDiagramRaw_proxy_climb_between selection layout terminal proxy hle

theorem extractDiagramRaw_bodyContainer_climb
    (d : ConcreteDiagram) (selection : CheckedSelection d)
    (layout : FragmentLayout d selection) :
    (d.extractDiagramRaw selection layout).climb layout.proxyCount
        layout.bodyContainer = some layout.root := by
  by_cases hzero : layout.proxyCount = 0
  · rw [layout.bodyContainer_eq_root_of_proxyCount_eq_zero hzero, hzero]
    rfl
  ·
    let terminal : Fin layout.proxyCount :=
      ⟨layout.proxyCount - 1, by omega⟩
    have hbody : layout.bodyContainer = layout.proxy terminal :=
      layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hzero
    have hclimb := d.extractDiagramRaw_proxy_climb selection layout terminal
    have hsteps : terminal.val + 1 = layout.proxyCount := by
      simp [terminal]
      omega
    rw [hbody]
    calc
      (d.extractDiagramRaw selection layout).climb layout.proxyCount
          (layout.proxy terminal) =
        (d.extractDiagramRaw selection layout).climb (terminal.val + 1)
          (layout.proxy terminal) := congrArg
            (fun steps => (d.extractDiagramRaw selection layout).climb steps
              (layout.proxy terminal)) hsteps.symm
      _ = some layout.root := hclimb

theorem extractDiagramRaw_all_regions_reach_root
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).AllRegionsReachRoot := by
  intro region
  rcases host.val.extractDiagramRaw_region_cases selection layout region with
    hroot | hproxy | hmaterial
  · subst region
    exact ConcreteDiagram.Encloses.refl _ _
  · obtain ⟨index, rfl⟩ := hproxy
    refine ⟨⟨index.val + 1, by
      simp only [extractDiagramRaw, FragmentLayout.regionCount]
      omega⟩, ?_⟩
    exact host.val.extractDiagramRaw_proxy_climb selection layout index
  · obtain ⟨index, rfl⟩ := hmaterial
    obtain ⟨child, hchild, steps, hhostClimb⟩ :=
      (selection.mem_selectedRegions
        (selection.selectedRegions.get index)).1 (List.get_mem _ _)
    have hchildSelected : child ∈ selection.selectedRegions :=
      (selection.mem_selectedRegions child).2
        ⟨child, hchild, ConcreteDiagram.Encloses.refl host.val child⟩
    obtain ⟨childIndex, hchildGet, hmaterialClimb⟩ :=
      extractDiagramRaw_climb_selected host selection layout hchildSelected index
        steps.val steps.isLt hhostClimb
    have hstepBound :=
      extractDiagramRaw_climb_selected_steps_lt_materialRegionCount host
        selection layout hchildSelected index steps.val steps.isLt hhostClimb
    have hchildParent :
        (host.val.regions
          (selection.selectedRegions.get childIndex)).parent? =
        some selection.val.anchor := by
      rw [hchildGet]
      exact selection.property.childRoots_direct child hchild
    have hchildBody :
        (host.val.extractDiagramRaw selection layout).climb 1
            (layout.materialRegion childIndex) =
          some layout.bodyContainer := by
      simp only [ConcreteDiagram.climb]
      rw [extractDiagramRaw_materialRegion_parent_exact host selection layout
        childIndex hchildParent]
      rw [host.val.fragmentParent_anchor selection layout]
      rfl
    have hmaterialBody :=
      ConcreteElaboration.climb_add hmaterialClimb hchildBody
    have hbodyRoot :=
      host.val.extractDiagramRaw_bodyContainer_climb selection layout
    have hmaterialRoot :=
      ConcreteElaboration.climb_add hmaterialBody hbodyRoot
    refine ⟨⟨steps.val + 1 + layout.proxyCount, by
      simp only [extractDiagramRaw, FragmentLayout.regionCount]
      omega⟩, ?_⟩
    exact hmaterialRoot

theorem extractDiagramRaw_encloses_selected
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (ancestor descendant : Fin layout.materialRegionCount)
    (hencloses : host.val.Encloses
      (selection.selectedRegions.get ancestor)
      (selection.selectedRegions.get descendant)) :
    (host.val.extractDiagramRaw selection layout).Encloses
      (layout.materialRegion ancestor) (layout.materialRegion descendant) := by
  obtain ⟨steps, hhostClimb⟩ := hencloses
  obtain ⟨finishIndex, hfinishGet, hfragmentClimb⟩ :=
    extractDiagramRaw_climb_selected host selection layout
      (List.get_mem _ ancestor) descendant steps.val steps.isLt hhostClimb
  have hfinishIndex : finishIndex = ancestor := by
    apply Fin.ext
    exact (List.getElem_inj selection.selectedRegions_nodup).mp (by
      simpa only [List.get_eq_getElem] using hfinishGet)
  subst finishIndex
  have hbound :=
    extractDiagramRaw_climb_selected_steps_lt_materialRegionCount host
      selection layout (List.get_mem _ ancestor) descendant steps.val
        steps.isLt hhostClimb
  refine ⟨⟨steps.val, by
    simp only [extractDiagramRaw, FragmentLayout.regionCount]
    omega⟩, hfragmentClimb⟩

theorem extractDiagramRaw_bodyContainer_encloses_materialRegion
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (index : Fin layout.materialRegionCount) :
    (host.val.extractDiagramRaw selection layout).Encloses
      layout.bodyContainer (layout.materialRegion index) := by
  obtain ⟨child, hchild, steps, hhostClimb⟩ :=
    (selection.mem_selectedRegions
      (selection.selectedRegions.get index)).1 (List.get_mem _ _)
  have hchildSelected : child ∈ selection.selectedRegions :=
    (selection.mem_selectedRegions child).2
      ⟨child, hchild, ConcreteDiagram.Encloses.refl host.val child⟩
  obtain ⟨childIndex, hchildGet, hmaterialClimb⟩ :=
    extractDiagramRaw_climb_selected host selection layout hchildSelected index
      steps.val steps.isLt hhostClimb
  have hstepBound :=
    extractDiagramRaw_climb_selected_steps_lt_materialRegionCount host
      selection layout hchildSelected index steps.val steps.isLt hhostClimb
  have hchildParent :
      (host.val.regions
        (selection.selectedRegions.get childIndex)).parent? =
      some selection.val.anchor := by
    rw [hchildGet]
    exact selection.property.childRoots_direct child hchild
  have hchildBody :
      (host.val.extractDiagramRaw selection layout).climb 1
          (layout.materialRegion childIndex) =
        some layout.bodyContainer := by
    simp only [ConcreteDiagram.climb]
    rw [extractDiagramRaw_materialRegion_parent_exact host selection layout
      childIndex hchildParent]
    rw [host.val.fragmentParent_anchor selection layout]
    rfl
  refine ⟨⟨steps.val + 1, by
    simp only [extractDiagramRaw, FragmentLayout.regionCount]
    omega⟩, ?_⟩
  exact ConcreteElaboration.climb_add hmaterialClimb hchildBody

theorem extractDiagramRaw_proxy_encloses_materialRegion
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection)
    (proxy : Fin layout.proxyCount)
    (index : Fin layout.materialRegionCount) :
    (host.val.extractDiagramRaw selection layout).Encloses
      (layout.proxy proxy) (layout.materialRegion index) := by
  obtain ⟨child, hchild, steps, hhostClimb⟩ :=
    (selection.mem_selectedRegions
      (selection.selectedRegions.get index)).1 (List.get_mem _ _)
  have hchildSelected : child ∈ selection.selectedRegions :=
    (selection.mem_selectedRegions child).2
      ⟨child, hchild, ConcreteDiagram.Encloses.refl host.val child⟩
  obtain ⟨childIndex, hchildGet, hmaterialClimb⟩ :=
    extractDiagramRaw_climb_selected host selection layout hchildSelected index
      steps.val steps.isLt hhostClimb
  have hstepBound :=
    extractDiagramRaw_climb_selected_steps_lt_materialRegionCount host
      selection layout hchildSelected index steps.val steps.isLt hhostClimb
  have hchildParent :
      (host.val.regions
        (selection.selectedRegions.get childIndex)).parent? =
      some selection.val.anchor := by
    rw [hchildGet]
    exact selection.property.childRoots_direct child hchild
  have hchildBody :
      (host.val.extractDiagramRaw selection layout).climb 1
          (layout.materialRegion childIndex) =
        some layout.bodyContainer := by
    simp only [ConcreteDiagram.climb]
    rw [extractDiagramRaw_materialRegion_parent_exact host selection layout
      childIndex hchildParent]
    rw [host.val.fragmentParent_anchor selection layout]
    rfl
  have hmaterialBody :=
    ConcreteElaboration.climb_add hmaterialClimb hchildBody
  have hnonzero : layout.proxyCount ≠ 0 := by
    have := proxy.isLt
    omega
  let terminal : Fin layout.proxyCount :=
    ⟨layout.proxyCount - 1, by omega⟩
  have hbody : layout.bodyContainer = layout.proxy terminal :=
    layout.bodyContainer_eq_terminal_of_proxyCount_ne_zero hnonzero
  have hle : proxy.val ≤ terminal.val := by
    simp [terminal]
    omega
  have hbodyProxy :
      (host.val.extractDiagramRaw selection layout).climb
          (terminal.val - proxy.val) layout.bodyContainer =
        some (layout.proxy proxy) := by
    rw [hbody]
    exact host.val.extractDiagramRaw_proxy_climb_between selection layout
      terminal proxy hle
  refine ⟨⟨steps.val + 1 + (terminal.val - proxy.val), by
    simp only [extractDiagramRaw, FragmentLayout.regionCount]
    have hterminal : terminal.val < layout.proxyCount := terminal.isLt
    omega⟩, ?_⟩
  exact ConcreteElaboration.climb_add hmaterialBody hbodyProxy

theorem extractDiagramRaw_atom_binders_are_bubbles
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).AtomBindersAreBubbles := by
  intro node
  rw [host.val.extractDiagramRaw_node selection layout node]
  cases hnode : host.val.nodes (selection.selectedNodes.get node) with
  | term region freePorts term =>
      unfold fragmentNode
      rw [hnode]
      trivial
  | named region definition arity =>
      unfold fragmentNode
      rw [hnode]
      trivial
  | atom region binder =>
      obtain ⟨_, extractedParent, arity, _, hextracted⟩ :=
        extractDiagramRaw_atom_binder_bubble host selection layout node hnode
      unfold fragmentNode
      rw [hnode]
      simp only
      exact ⟨extractedParent, arity, hextracted⟩

theorem extractDiagramRaw_named_references_resolve
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).NamedReferencesResolve
      signature := by
  intro node
  rw [host.val.extractDiagramRaw_node selection layout node]
  cases hnode : host.val.nodes (selection.selectedNodes.get node) with
  | term region freePorts term =>
      unfold fragmentNode
      rw [hnode]
      trivial
  | atom region binder =>
      unfold fragmentNode
      rw [hnode]
      trivial
  | named region definition arity =>
      have hresolve := host.property.named_references_resolve
        (selection.selectedNodes.get node)
      simp only [hnode] at hresolve
      unfold fragmentNode
      rw [hnode]
      exact hresolve

theorem extractDiagramRaw_atom_binders_enclose
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).AtomBindersEnclose := by
  intro node
  rw [host.val.extractDiagramRaw_node selection layout node]
  cases hnode : host.val.nodes (selection.selectedNodes.get node) with
  | term region freePorts term =>
      unfold fragmentNode
      rw [hnode]
      trivial
  | named region definition arity =>
      unfold fragmentNode
      rw [hnode]
      trivial
  | atom region binder =>
      have hhostEncloses := host.property.atom_binders_enclose
        (selection.selectedNodes.get node)
      simp only [hnode] at hhostEncloses
      unfold fragmentNode
      rw [hnode]
      simp only
      by_cases hselectedBinder : binder ∈ selection.selectedRegions
      · have hselectedRegion : region ∈ selection.selectedRegions :=
          (selection.mem_selectedRegions region).2
            (selectsRegion_downward host.property
              ((selection.mem_selectedRegions binder).1 hselectedBinder)
              hhostEncloses)
        obtain ⟨binderIndex, hbinderGet, hbinderFragment⟩ :=
          fragmentParent_selectedRegion host selection layout hselectedBinder
        obtain ⟨regionIndex, hregionGet, hregionFragment⟩ :=
          fragmentParent_selectedRegion host selection layout hselectedRegion
        have hmapped := extractDiagramRaw_encloses_selected host selection
          layout binderIndex regionIndex (by
            rw [hbinderGet, hregionGet]
            exact hhostEncloses)
        have hfragmentBinder : host.val.fragmentBinder layout binder =
            layout.materialRegion binderIndex := by
          unfold fragmentBinder
          obtain ⟨found, hfound⟩ := indexOf?_complete hselectedBinder
          have hindex : found = binderIndex := by
            apply Fin.ext
            exact (List.getElem_inj selection.selectedRegions_nodup).mp (by
              simpa only [List.get_eq_getElem] using
                (indexOf?_sound hfound).trans hbinderGet.symm)
          subst found
          rw [hfound]
        rw [hfragmentBinder, hregionFragment]
        exact hmapped
      · have huses : selection.UsesExternalBinder binder :=
          ⟨hselectedBinder, selection.selectedNodes.get node,
            List.get_mem _ _, by simpa only [hnode]⟩
        have hexternal : binder ∈ layout.externalBinders := by
          rw [layout.externalBinders_exact]
          exact (selection.mem_externalBinders_iff_uses host binder).2 huses
        obtain ⟨proxy, hproxy⟩ := indexOf?_complete hexternal
        have hproxyGet : layout.externalBinders.get proxy = binder :=
          indexOf?_sound hproxy
        have hfragmentBinder : host.val.fragmentBinder layout binder =
            layout.proxy proxy := by
          rw [← hproxyGet]
          exact fragmentBinder_externalBinder host selection layout proxy
        rw [hfragmentBinder]
        rcases (selection.mem_selectedNodes
          (selection.selectedNodes.get node)).1 (List.get_mem _ _) with
          hdirect | hsubtree
        · have hregionAnchor := selection.property.directNodes_at_anchor
            (selection.selectedNodes.get node) hdirect
          simp only [hnode, CNode.region] at hregionAnchor
          rw [hregionAnchor, host.val.fragmentParent_anchor selection layout]
          exact host.val.extractDiagramRaw_proxy_encloses_bodyContainer
            selection layout proxy
        · have hselectedRegion : region ∈ selection.selectedRegions :=
            (selection.mem_selectedRegions region).2 (by
              simpa only [hnode, CNode.region] using hsubtree)
          obtain ⟨regionIndex, hregionGet, hregionFragment⟩ :=
            fragmentParent_selectedRegion host selection layout hselectedRegion
          rw [hregionFragment]
          exact extractDiagramRaw_proxy_encloses_materialRegion host
            selection layout proxy regionIndex

theorem extractDiagramRaw_required_ports_are_covered
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).RequiredPortsAreCovered := by
  intro node
  rw [host.val.extractDiagramRaw_node selection layout node]
  cases hnode : host.val.nodes (selection.selectedNodes.get node) with
  | term region freePorts term =>
      have hcovered := host.property.required_ports_are_covered
        (selection.selectedNodes.get node)
      simp only [hnode] at hcovered
      unfold fragmentNode
      rw [hnode]
      simp only
      constructor
      · obtain ⟨wire, hwire⟩ := hcovered.1
        exact extractDiagramRaw_endpointOccurs_of_selected host selection layout
          node .output hwire
      · intro port
        obtain ⟨wire, hwire⟩ := hcovered.2 port
        exact extractDiagramRaw_endpointOccurs_of_selected host selection layout
          node (.free port) hwire
  | named region definition arity =>
      have hcovered := host.property.required_ports_are_covered
        (selection.selectedNodes.get node)
      simp only [hnode] at hcovered
      unfold fragmentNode
      rw [hnode]
      simp only
      intro port
      obtain ⟨wire, hwire⟩ := hcovered port
      exact extractDiagramRaw_endpointOccurs_of_selected host selection layout
        node (.arg port) hwire
  | atom region binder =>
      obtain ⟨hostParent, extractedParent, arity, hhostBinder,
          hextractedBinder⟩ :=
        extractDiagramRaw_atom_binder_bubble host selection layout node hnode
      have hcovered := host.property.required_ports_are_covered
        (selection.selectedNodes.get node)
      simp only [hnode, hhostBinder] at hcovered
      unfold fragmentNode
      rw [hnode]
      simp only
      rw [hextractedBinder]
      simp only
      intro port
      obtain ⟨wire, hwire⟩ := hcovered port
      exact extractDiagramRaw_endpointOccurs_of_selected host selection layout
        node (.arg port) hwire

theorem extractDiagramRaw_wire_scopes_enclose
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).WireScopesEnclose := by
  intro wire
  revert wire
  apply Fin.addCases
  · intro internal endpoint hendpoint
    let originalWire := selection.internalWires.get internal
    obtain ⟨originalEndpoint, horiginalMember, hmapped⟩ :=
      (host.val.mem_extractDiagramRaw_wire_endpoints_iff selection layout
        (layout.internalWire internal) endpoint).1 hendpoint
    have horigin := fragmentEndpoint?_origin selection hmapped
    rw [horigin] at horiginalMember
    have horiginalWire : fragmentWireOrigin selection layout
        (layout.internalWire internal) = originalWire := by
      simp [fragmentWireOrigin, FragmentLayout.internalWire, originalWire]
    rw [horiginalWire] at horiginalMember
    have hhostEncloses := host.property.wire_scopes_enclose originalWire
      ({ node := selection.selectedNodes.get endpoint.node,
          port := endpoint.port } : CEndpoint host.val.nodeCount)
      horiginalMember
    have hscopeExact :
        ((host.val.extractDiagramRaw selection layout).wires
          (Fin.castAdd layout.boundaryWireCount internal)).scope =
        host.val.fragmentParent layout (host.val.wires originalWire).scope := by
      simp [extractDiagramRaw, fragmentWire, fragmentInternalWire,
        originalWire]
    rw [hscopeExact,
      host.val.extractDiagramRaw_node_region selection layout endpoint.node]
    rcases (selection.mem_internalWires_expanded originalWire).1
        (List.get_mem _ internal) with hselectedScope | hexplicit
    · have hselectedNodeRegion :
          (host.val.nodes
            (selection.selectedNodes.get endpoint.node)).region ∈
            selection.selectedRegions :=
        (selection.mem_selectedRegions _).2
          (selectsRegion_downward host.property hselectedScope hhostEncloses)
      obtain ⟨scopeIndex, hscopeGet, hscopeFragment⟩ :=
        fragmentParent_selectedRegion host selection layout
          ((selection.mem_selectedRegions _).2 hselectedScope)
      obtain ⟨regionIndex, hregionGet, hregionFragment⟩ :=
        fragmentParent_selectedRegion host selection layout hselectedNodeRegion
      rw [hscopeFragment, hregionFragment]
      exact extractDiagramRaw_encloses_selected host selection layout
        scopeIndex regionIndex (by
          rw [hscopeGet, hregionGet]
          exact hhostEncloses)
    · have hscopeAnchor := selection.property.explicitWires_at_anchor
          originalWire hexplicit
      rw [hscopeAnchor, host.val.fragmentParent_anchor selection layout]
      rcases (selection.mem_selectedNodes
        (selection.selectedNodes.get endpoint.node)).1 (List.get_mem _ _) with
        hdirect | hsubtree
      · have hownerAnchor := selection.property.directNodes_at_anchor
          (selection.selectedNodes.get endpoint.node) hdirect
        rw [hownerAnchor, host.val.fragmentParent_anchor selection layout]
        exact ConcreteDiagram.Encloses.refl _ _
      · have hselectedRegion :
            (host.val.nodes
              (selection.selectedNodes.get endpoint.node)).region ∈
              selection.selectedRegions :=
          (selection.mem_selectedRegions _).2 hsubtree
        obtain ⟨regionIndex, hregionGet, hregionFragment⟩ :=
          fragmentParent_selectedRegion host selection layout hselectedRegion
        rw [hregionFragment]
        exact extractDiagramRaw_bodyContainer_encloses_materialRegion host
          selection layout regionIndex
  · intro boundary endpoint hendpoint
    have hscopeExact :
        ((host.val.extractDiagramRaw selection layout).wires
          (Fin.natAdd layout.internalWireCount boundary)).scope = layout.root := by
      simp [extractDiagramRaw, fragmentWire, fragmentBoundaryWire]
    rw [hscopeExact]
    exact extractDiagramRaw_all_regions_reach_root host selection layout
      ((host.val.extractDiagramRaw selection layout).nodes endpoint.node).region
theorem extractDiagramRaw_only_root_is_sheet
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).OnlyRootIsSheet := by
  intro region hsheet
  rcases host.val.extractDiagramRaw_region_cases selection layout region with
    hroot | hproxy | hmaterial
  · exact hroot
  · obtain ⟨index, rfl⟩ := hproxy
    rw [host.val.extractDiagramRaw_proxy_region selection layout index] at hsheet
    contradiction
  · obtain ⟨index, rfl⟩ := hmaterial
    rw [host.val.extractDiagramRaw_materialRegion selection layout index] at hsheet
    unfold fragmentMaterialRegion at hsheet
    split at hsheet
    · rename_i hkind
      have hroot := host.property.only_root_is_sheet
        (selection.selectedRegions.get index) hkind
      exact False.elim
        (selectedRegion_ne_root host selection (List.get_mem _ _) hroot)
    · contradiction
    · contradiction

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

/-- Extraction preserves every concrete well-formedness clause. -/
theorem extractDiagramRaw_wellFormed
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractDiagramRaw selection layout).WellFormed signature where
  root_is_sheet := host.val.extractDiagramRaw_root_region selection layout
  only_root_is_sheet :=
    extractDiagramRaw_only_root_is_sheet host selection layout
  all_regions_reach_root :=
    extractDiagramRaw_all_regions_reach_root host selection layout
  atom_binders_are_bubbles :=
    extractDiagramRaw_atom_binders_are_bubbles host selection layout
  atom_binders_enclose :=
    extractDiagramRaw_atom_binders_enclose host selection layout
  named_references_resolve :=
    extractDiagramRaw_named_references_resolve host selection layout
  endpoints_are_valid :=
    extractDiagramRaw_endpoints_are_valid host selection layout
  endpoints_are_nodup :=
    extractDiagramRaw_endpoints_are_nodup host selection layout
  wire_endpoints_are_disjoint :=
    extractDiagramRaw_wire_endpoints_are_disjoint host selection layout
  required_ports_are_covered :=
    extractDiagramRaw_required_ports_are_covered host selection layout
  wire_scopes_enclose :=
    extractDiagramRaw_wire_scopes_enclose host selection layout

theorem extractOpenRaw_wellFormed
    (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val)
    (layout : FragmentLayout host.val selection) :
    (host.val.extractOpenRaw selection layout).WellFormed signature where
  diagram_well_formed :=
    extractDiagramRaw_wellFormed host selection layout
  boundary_is_root_scoped :=
    host.val.extractBoundaryRaw_root_scoped selection layout

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

theorem check_complete {signature : List Nat}
    {host : CheckedDiagram signature}
    {selection : CheckedSelection host.val}
    (raw : RawExtraction host.val selection) :
    ∃ extraction, raw.check = .ok extraction := by
  have hwf : raw.fragment.diagram.WellFormed signature := by
    rw [raw.fragment_exact]
    exact ConcreteDiagram.extractDiagramRaw_wellFormed host selection raw.layout
  unfold check
  split
  · rename_i error hcheck
    rw [checkWellFormed_complete hwf] at hcheck
    contradiction
  · exact ⟨_, rfl⟩

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

theorem extractChecked_complete
    (signature : List Nat) (host : CheckedDiagram signature)
    (selection : CheckedSelection host.val) :
    ∃ extraction, extractChecked signature host selection = .ok extraction := by
  exact RawExtraction.check_complete
    ({} : RawExtraction host.val selection)

end VisualProof.Diagram
