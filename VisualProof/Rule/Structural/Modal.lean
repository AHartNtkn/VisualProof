import VisualProof.Rule.Structural.Wire

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

def doubleCutIntroRaw (input : ConcreteDiagram)
    (selection : CheckedSelection input) : ConcreteDiagram :=
  let outer : Fin (input.regionCount + 2) :=
    Fin.natAdd input.regionCount ⟨0, by decide⟩
  let inner : Fin (input.regionCount + 2) :=
    Fin.natAdd input.regionCount ⟨1, by decide⟩
  { regionCount := input.regionCount + 2
    nodeCount := input.nodeCount
    wireCount := input.wireCount
    root := Fin.castAdd 2 input.root
    regions := Fin.addCases
      (fun region =>
        if region ∈ selection.val.childRoots then
          reparentLiftedRegion 2 inner (input.regions region)
        else
          liftCRegion 2 (input.regions region))
      (Fin.cases (.cut (Fin.castAdd 2 selection.val.anchor))
        (fun _ => .cut outer))
    nodes := fun node =>
      if node ∈ selection.val.directNodes then
        reparentLiftedNode 2 inner (input.nodes node)
      else
        liftCNode 2 (input.nodes node)
    wires := fun wire => liftCWireRegions 2 (input.wires wire) }

def doubleCutIntroWireProvenance (input : ConcreteDiagram)
    (selection : CheckedSelection input) :
    WireProvenance input (doubleCutIntroRaw input selection) :=
  WireProvenance.rootFiltered input (doubleCutIntroRaw input selection)
    (fun wire => some wire) (by
      intro left right mapped hleft hright
      simpa only [Option.some.injEq] using hleft.trans hright.symm)

def doubleCutIntroInterfaceTransport (input : ConcreteDiagram)
    (selection : CheckedSelection input) :
    InterfaceTransport input (doubleCutIntroRaw input selection) :=
  InterfaceTransport.byWireCount input (doubleCutIntroRaw input selection) rfl

def applyDoubleCutIntro (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    Except StepError (StepReceipt input) :=
  match hcheck : checkWellFormed signature
      (doubleCutIntroRaw input.val selection) with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (StepReceipt.ofChecked input
      (doubleCutIntroRaw input.val selection)
      (doubleCutIntroWireProvenance input.val selection)
      (doubleCutIntroInterfaceTransport input.val selection) result hcheck)

theorem applyDoubleCutIntro_preserves_raw
    (happly : applyDoubleCutIntro input selection = .ok result) :
    result.result.val = doubleCutIntroRaw input.val selection := by
  unfold applyDoubleCutIntro at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact checkWellFormed_preserves_input hcheck

theorem applyDoubleCutIntro_realizes
    (happly : applyDoubleCutIntro input selection = .ok result) :
    result.Realizes (doubleCutIntroRaw input.val selection)
      (doubleCutIntroWireProvenance input.val selection)
      (doubleCutIntroInterfaceTransport input.val selection) := by
  unfold applyDoubleCutIntro at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

def doubleCutRegionDomain (input : ConcreteDiagram)
    (outer inner : Fin input.regionCount) : SurvivorDomain input.regionCount where
  survives region := decide (region ≠ outer ∧ region ≠ inner)

def promoteRegion? (domain : SurvivorDomain regions)
    (inner target : Fin regions) : CRegion regions → Option (CRegion domain.count)
  | .sheet => some .sheet
  | .cut parent =>
      if parent = inner then
        (domain.index? target).map CRegion.cut
      else
        (domain.index? parent).map CRegion.cut
  | .bubble parent arity =>
      if parent = inner then
        (domain.index? target).map fun mapped => .bubble mapped arity
      else
        (domain.index? parent).map fun mapped => .bubble mapped arity

def promoteNode? (domain : SurvivorDomain regions)
    (inner target : Fin regions) : CNode regions → Option (CNode domain.count)
  | .term region freePorts term =>
      let owner := if region = inner then target else region
      (domain.index? owner).map fun mapped => .term mapped freePorts term
  | .atom region binder => do
      let owner := if region = inner then target else region
      let mappedOwner ← domain.index? owner
      let mappedBinder ← domain.index? binder
      pure (.atom mappedOwner mappedBinder)
  | .named region definition arity =>
      let owner := if region = inner then target else region
      (domain.index? owner).map fun mapped => .named mapped definition arity

def promoteWire? (domain : SurvivorDomain regions)
    (inner target : Fin regions) (wire : CWire regions nodes) :
    Option (CWire domain.count nodes) := do
  let scope := if wire.scope = inner then target else wire.scope
  let mapped ← domain.index? scope
  pure { scope := mapped, endpoints := wire.endpoints }

def promoteDiagramRaw? (input : ConcreteDiagram)
    (domain : SurvivorDomain input.regionCount)
    (removed target : Fin input.regionCount) :
    Option { raw : ConcreteDiagram // raw.wireCount = input.wireCount } := do
  let root ← domain.index? input.root
  let regions ← sequenceFin fun region =>
    promoteRegion? domain removed target (input.regions (domain.origin region))
  let nodes ← sequenceFin fun node =>
    promoteNode? domain removed target (input.nodes node)
  let wires ← sequenceFin fun wire =>
    promoteWire? domain removed target (input.wires wire)
  pure ⟨{
    regionCount := domain.count
    nodeCount := input.nodeCount
    wireCount := input.wireCount
    root := root
    regions := regions
    nodes := nodes
    wires := wires
  }, rfl⟩

structure PromoteDiagramTrace
    (input : ConcreteDiagram)
    (domain : SurvivorDomain input.regionCount)
    (removed target : Fin input.regionCount)
    (raw : ConcreteDiagram) where
  root : Fin domain.count
  regions : Fin domain.count → CRegion domain.count
  nodes : Fin input.nodeCount → CNode domain.count
  wires : Fin input.wireCount → CWire domain.count input.nodeCount
  root_result : domain.index? input.root = some root
  regions_result :
    sequenceFin (fun region =>
      promoteRegion? domain removed target
        (input.regions (domain.origin region))) =
      some regions
  nodes_result :
    sequenceFin (fun node =>
      promoteNode? domain removed target (input.nodes node)) =
      some nodes
  wires_result :
    sequenceFin (fun wire =>
      promoteWire? domain removed target (input.wires wire)) =
      some wires
  raw_eq : raw = {
    regionCount := domain.count
    nodeCount := input.nodeCount
    wireCount := input.wireCount
    root := root
    regions := regions
    nodes := nodes
    wires := wires
  }

def PromoteDiagramTrace.diagram
    (trace : PromoteDiagramTrace input domain removed target raw) :
    ConcreteDiagram where
  regionCount := domain.count
  nodeCount := input.nodeCount
  wireCount := input.wireCount
  root := trace.root
  regions := trace.regions
  nodes := trace.nodes
  wires := trace.wires

theorem PromoteDiagramTrace.raw_eq_diagram
    (trace : PromoteDiagramTrace input domain removed target raw) :
    raw = trace.diagram :=
  trace.raw_eq

theorem promoteDiagramRaw?_trace
    (hraw : (promoteDiagramRaw? input domain removed target).map
      Subtype.val = some raw) :
    Nonempty (PromoteDiagramTrace input domain removed target raw) := by
  rw [Option.map_eq_some_iff] at hraw
  obtain ⟨result, promoted, rawEq⟩ := hraw
  subst raw
  unfold promoteDiagramRaw? at promoted
  change (domain.index? input.root).bind (fun root =>
      (sequenceFin fun region =>
        promoteRegion? domain removed target
          (input.regions (domain.origin region))).bind (fun regions =>
      (sequenceFin fun node =>
        promoteNode? domain removed target (input.nodes node)).bind
        (fun nodes =>
      (sequenceFin fun wire =>
        promoteWire? domain removed target (input.wires wire)).bind
        (fun wires => some ⟨{
          regionCount := domain.count
          nodeCount := input.nodeCount
          wireCount := input.wireCount
          root
          regions
          nodes
          wires
        }, rfl⟩)))) = some result at promoted
  rw [Option.bind_eq_some_iff] at promoted
  obtain ⟨root, rootResult, promoted⟩ := promoted
  rw [Option.bind_eq_some_iff] at promoted
  obtain ⟨regions, regionsResult, promoted⟩ := promoted
  rw [Option.bind_eq_some_iff] at promoted
  obtain ⟨nodes, nodesResult, promoted⟩ := promoted
  rw [Option.bind_eq_some_iff] at promoted
  obtain ⟨wires, wiresResult, resultEq⟩ := promoted
  cases resultEq
  exact ⟨{
    root
    regions
    nodes
    wires
    root_result := rootResult
    regions_result := regionsResult
    nodes_result := nodesResult
    wires_result := wiresResult
    raw_eq := rfl
  }⟩

theorem PromoteDiagramTrace.root_origin
    (trace : PromoteDiagramTrace input domain removed target raw) :
    domain.origin trace.root = input.root :=
  (domain.index?_eq_some_iff input.root trace.root).1 trace.root_result

theorem PromoteDiagramTrace.region_result
    (trace : PromoteDiagramTrace input domain removed target raw)
    (region : Fin domain.count) :
    promoteRegion? domain removed target
        (input.regions (domain.origin region)) =
      some (trace.regions region) :=
  sequenceFin_sound trace.regions_result region

theorem PromoteDiagramTrace.node_result
    (trace : PromoteDiagramTrace input domain removed target raw)
    (node : Fin input.nodeCount) :
    promoteNode? domain removed target (input.nodes node) =
      some (trace.nodes node) :=
  sequenceFin_sound trace.nodes_result node

theorem PromoteDiagramTrace.wire_result
    (trace : PromoteDiagramTrace input domain removed target raw)
    (wire : Fin input.wireCount) :
    promoteWire? domain removed target (input.wires wire) =
      some (trace.wires wire) :=
  sequenceFin_sound trace.wires_result wire

@[simp] theorem PromoteDiagramTrace.raw_regionCount
    (trace : PromoteDiagramTrace input domain removed target raw) :
    raw.regionCount = domain.count := by
  rw [trace.raw_eq]

@[simp] theorem PromoteDiagramTrace.raw_nodeCount
    (trace : PromoteDiagramTrace input domain removed target raw) :
    raw.nodeCount = input.nodeCount := by
  rw [trace.raw_eq]

@[simp] theorem PromoteDiagramTrace.raw_wireCount
    (trace : PromoteDiagramTrace input domain removed target raw) :
    raw.wireCount = input.wireCount := by
  rw [trace.raw_eq]

theorem PromoteDiagramTrace.raw_root
    (trace : PromoteDiagramTrace input domain removed target raw) :
    HEq raw.root trace.root := by
  cases trace with
  | mk root regions nodes wires rootResult regionsResult nodesResult
      wiresResult rawEq =>
      subst raw
      rfl

theorem PromoteDiagramTrace.raw_region
    (trace : PromoteDiagramTrace input domain removed target raw)
    (region : Fin domain.count) :
    HEq
      (raw.regions (Fin.cast trace.raw_regionCount.symm region))
      (trace.regions region) := by
  cases trace with
  | mk root regions nodes wires rootResult regionsResult nodesResult
      wiresResult rawEq =>
      subst raw
      rfl

theorem PromoteDiagramTrace.raw_node
    (trace : PromoteDiagramTrace input domain removed target raw)
    (node : Fin input.nodeCount) :
    HEq
      (raw.nodes (Fin.cast trace.raw_nodeCount.symm node))
      (trace.nodes node) := by
  cases trace with
  | mk root regions nodes wires rootResult regionsResult nodesResult
      wiresResult rawEq =>
      subst raw
      rfl

theorem PromoteDiagramTrace.raw_wire
    (trace : PromoteDiagramTrace input domain removed target raw)
    (wire : Fin input.wireCount) :
    HEq
      (raw.wires (Fin.cast trace.raw_wireCount.symm wire))
      (trace.wires wire) := by
  cases trace with
  | mk root regions nodes wires rootResult regionsResult nodesResult
      wiresResult rawEq =>
      subst raw
      rfl

private theorem promoteDiagramRaw?_wireCount
    (hraw : (promoteDiagramRaw? input domain removed target).map
      Subtype.val = some raw) :
    raw.wireCount = input.wireCount := by
  rw [Option.map_eq_some_iff] at hraw
  obtain ⟨witness, _, rfl⟩ := hraw
  exact witness.property

def doubleCutElimRaw? (input : ConcreteDiagram)
    (outer : Fin input.regionCount) : Option ConcreteDiagram :=
  match input.regions outer with
  | .sheet | .bubble .. => none
  | .cut target =>
      let children := filterFin fun region =>
        decide ((input.regions region).parent? = some outer)
      match children with
      | [inner] =>
          match input.regions inner with
          | .cut parent =>
              if parent = outer &&
                  (filterFin fun node =>
                    decide ((input.nodes node).region = outer)).isEmpty &&
                  (filterFin fun wire =>
                    decide ((input.wires wire).scope = outer)).isEmpty then do
                let domain := doubleCutRegionDomain input outer inner
                (promoteDiagramRaw? input domain inner target).map Subtype.val
              else none
          | _ => none
      | _ => none

theorem doubleCutElimRaw?_spec
    (hraw : doubleCutElimRaw? input outer = some raw) :
    ∃ target inner,
      input.regions outer = .cut target ∧
      filterFin (fun region =>
        decide ((input.regions region).parent? = some outer)) = [inner] ∧
      input.regions inner = .cut outer ∧
      (filterFin fun node =>
        decide ((input.nodes node).region = outer)).isEmpty = true ∧
      (filterFin fun wire =>
        decide ((input.wires wire).scope = outer)).isEmpty = true ∧
      (promoteDiagramRaw? input
          (doubleCutRegionDomain input outer inner) inner target).map
          Subtype.val = some raw := by
  unfold doubleCutElimRaw? at hraw
  split at hraw <;> try contradiction
  · rename_i target outerShape
    dsimp only at hraw
    split at hraw <;> try contradiction
    · rename_i inner childrenEq
      split at hraw <;> try contradiction
      · rename_i parent innerShape
        split at hraw <;> try contradiction
        · rename_i conditions
          simp only [Bool.and_eq_true, decide_eq_true_eq] at conditions
          obtain ⟨⟨parentEq, nodesEmpty⟩, wiresEmpty⟩ := conditions
          subst parent
          exact ⟨target, inner, outerShape, childrenEq, innerShape,
            nodesEmpty, wiresEmpty, hraw⟩

structure DoubleCutElimTrace
    (input : ConcreteDiagram)
    (outer : Fin input.regionCount)
    (raw : ConcreteDiagram) where
  target : Fin input.regionCount
  inner : Fin input.regionCount
  outer_eq : input.regions outer = .cut target
  children_eq :
    filterFin (fun region =>
      decide ((input.regions region).parent? = some outer)) = [inner]
  inner_eq : input.regions inner = .cut outer
  outer_nodes_empty :
    (filterFin fun node =>
      decide ((input.nodes node).region = outer)).isEmpty = true
  outer_wires_empty :
    (filterFin fun wire =>
      decide ((input.wires wire).scope = outer)).isEmpty = true
  promotion : PromoteDiagramTrace input
    (doubleCutRegionDomain input outer inner) inner target raw

noncomputable def doubleCutElimTrace
    (hraw : doubleCutElimRaw? input outer = some raw) :
    DoubleCutElimTrace input outer raw := by
  let target := Classical.choose (doubleCutElimRaw?_spec hraw)
  let targetSpec := Classical.choose_spec (doubleCutElimRaw?_spec hraw)
  let inner := Classical.choose targetSpec
  have specification := Classical.choose_spec targetSpec
  exact {
    target
    inner
    outer_eq := specification.1
    children_eq := specification.2.1
    inner_eq := specification.2.2.1
    outer_nodes_empty := specification.2.2.2.1
    outer_wires_empty := specification.2.2.2.2.1
    promotion := Classical.choice (promoteDiagramRaw?_trace
      specification.2.2.2.2.2)
  }

theorem doubleCutElimRaw?_wireCount
    (hraw : doubleCutElimRaw? input outer = some raw) :
    raw.wireCount = input.wireCount := by
  unfold doubleCutElimRaw? at hraw
  repeat' first | split at hraw <;> try contradiction
  dsimp only at hraw
  repeat' first | split at hraw <;> try contradiction
  exact promoteDiagramRaw?_wireCount hraw

def doubleCutElimWireProvenance
    (hraw : doubleCutElimRaw? input outer = some raw) :
    WireProvenance input raw :=
  WireProvenance.byWireCount input raw
    (doubleCutElimRaw?_wireCount hraw).symm

def doubleCutElimInterfaceTransport
    (hraw : doubleCutElimRaw? input outer = some raw) :
    InterfaceTransport input raw :=
  InterfaceTransport.byWireCount input raw
    (doubleCutElimRaw?_wireCount hraw).symm

def applyDoubleCutElim (input : CheckedDiagram signature)
    (outer : Fin input.val.regionCount) :
    Except StepError (StepReceipt input) :=
  match hraw : doubleCutElimRaw? input.val outer with
  | none => .error .operationRejected
  | some raw =>
      match hcheck : checkWellFormed signature raw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (StepReceipt.ofChecked input raw
          (doubleCutElimWireProvenance hraw)
          (doubleCutElimInterfaceTransport hraw) result hcheck)

theorem applyDoubleCutElim_success_shape
    (happly : applyDoubleCutElim input outer = .ok result) :
    ∃ raw, doubleCutElimRaw? input.val outer = some raw ∧
      result.result.val = raw := by
  unfold applyDoubleCutElim at happly
  split at happly <;> try contradiction
  rename_i raw hraw
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨raw, hraw, checkWellFormed_preserves_input hcheck⟩

theorem applyDoubleCutElim_realizes
    (happly : applyDoubleCutElim input outer = .ok result) :
    ∃ raw, ∃ hraw : doubleCutElimRaw? input.val outer = some raw,
      result.Realizes raw (doubleCutElimWireProvenance hraw)
        (doubleCutElimInterfaceTransport hraw) := by
  unfold applyDoubleCutElim at happly
  split at happly <;> try contradiction
  rename_i raw hraw
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨raw, hraw, StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

def vacuousIntroRaw (input : ConcreteDiagram)
    (selection : CheckedSelection input) (arity : Nat) : ConcreteDiagram :=
  let bubble : Fin (input.regionCount + 1) := Fin.last input.regionCount
  { regionCount := input.regionCount + 1
    nodeCount := input.nodeCount
    wireCount := input.wireCount
    root := input.root.castSucc
    regions := Fin.lastCases
      (.bubble selection.val.anchor.castSucc arity)
      (fun region =>
        if region ∈ selection.val.childRoots then
          reparentLiftedRegion 1 bubble (input.regions region)
        else
          liftCRegion 1 (input.regions region))
    nodes := fun node =>
      if node ∈ selection.val.directNodes then
        reparentLiftedNode 1 bubble (input.nodes node)
      else
        liftCNode 1 (input.nodes node)
    wires := fun wire => liftCWireRegions 1 (input.wires wire) }

def vacuousIntroWireProvenance (input : ConcreteDiagram)
    (selection : CheckedSelection input) (arity : Nat) :
    WireProvenance input (vacuousIntroRaw input selection arity) :=
  WireProvenance.rootFiltered input (vacuousIntroRaw input selection arity)
    (fun wire => some wire) (by
      intro left right mapped hleft hright
      simpa only [Option.some.injEq] using hleft.trans hright.symm)

def vacuousIntroInterfaceTransport (input : ConcreteDiagram)
    (selection : CheckedSelection input) (arity : Nat) :
    InterfaceTransport input (vacuousIntroRaw input selection arity) :=
  InterfaceTransport.byWireCount input
    (vacuousIntroRaw input selection arity) rfl

def applyVacuousIntro (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (arity : Nat) :
    Except StepError (StepReceipt input) :=
  match hcheck : checkWellFormed signature
      (vacuousIntroRaw input.val selection arity) with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (StepReceipt.ofChecked input
      (vacuousIntroRaw input.val selection arity)
      (vacuousIntroWireProvenance input.val selection arity)
      (vacuousIntroInterfaceTransport input.val selection arity) result hcheck)

theorem applyVacuousIntro_preserves_raw
    (happly : applyVacuousIntro input selection arity = .ok result) :
    result.result.val = vacuousIntroRaw input.val selection arity := by
  unfold applyVacuousIntro at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact checkWellFormed_preserves_input hcheck

theorem applyVacuousIntro_realizes
    (happly : applyVacuousIntro input selection arity = .ok result) :
    result.Realizes (vacuousIntroRaw input.val selection arity)
      (vacuousIntroWireProvenance input.val selection arity)
      (vacuousIntroInterfaceTransport input.val selection arity) := by
  unfold applyVacuousIntro at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

def vacuousRegionDomain (input : ConcreteDiagram)
    (bubble : Fin input.regionCount) : SurvivorDomain input.regionCount where
  survives region := decide (region ≠ bubble)

def vacuousElimRaw? (input : ConcreteDiagram)
    (bubble : Fin input.regionCount) : Option ConcreteDiagram :=
  match input.regions bubble with
  | .sheet | .cut .. => none
  | .bubble parent _ =>
      if (filterFin fun node =>
          match input.nodes node with
          | .atom _ binder => decide (binder = bubble)
          | _ => false).isEmpty then do
        let domain := vacuousRegionDomain input bubble
        (promoteDiagramRaw? input domain bubble parent).map Subtype.val
      else none

theorem vacuousElimRaw?_spec
    (hraw : vacuousElimRaw? input bubble = some raw) :
    ∃ parent arity,
      input.regions bubble = .bubble parent arity ∧
      (filterFin fun node =>
        match input.nodes node with
        | .atom _ binder => decide (binder = bubble)
        | _ => false).isEmpty = true ∧
      (promoteDiagramRaw? input (vacuousRegionDomain input bubble)
          bubble parent).map Subtype.val =
        some raw := by
  unfold vacuousElimRaw? at hraw
  split at hraw <;> try contradiction
  · rename_i parent arity bubbleShape
    split at hraw <;> try contradiction
    rename_i empty
    exact ⟨parent, arity, bubbleShape, empty, hraw⟩

structure VacuousElimTrace
    (input : ConcreteDiagram)
    (bubble : Fin input.regionCount)
    (raw : ConcreteDiagram) where
  parent : Fin input.regionCount
  arity : Nat
  bubble_eq : input.regions bubble = .bubble parent arity
  bound_atoms_empty :
    (filterFin fun node =>
      match input.nodes node with
      | .atom _ binder => decide (binder = bubble)
      | _ => false).isEmpty = true
  promotion : PromoteDiagramTrace input
    (vacuousRegionDomain input bubble) bubble parent raw

noncomputable def vacuousElimTrace
    (hraw : vacuousElimRaw? input bubble = some raw) :
    VacuousElimTrace input bubble raw := by
  let parent := Classical.choose (vacuousElimRaw?_spec hraw)
  let parentSpec :=
    Classical.choose_spec (vacuousElimRaw?_spec hraw)
  let arity := Classical.choose parentSpec
  have specification := Classical.choose_spec parentSpec
  exact {
    parent
    arity
    bubble_eq := specification.1
    bound_atoms_empty := specification.2.1
    promotion := Classical.choice
      (promoteDiagramRaw?_trace specification.2.2)
  }

@[simp] theorem vacuousRegionDomain_survives
    (input : ConcreteDiagram) (bubble region : Fin input.regionCount) :
    (vacuousRegionDomain input bubble).survives region = true ↔
      region ≠ bubble := by
  simp [vacuousRegionDomain]

theorem VacuousElimTrace.origin_ne_bubble
    (_trace : VacuousElimTrace input bubble raw)
    (region : Fin (vacuousRegionDomain input bubble).count) :
    (vacuousRegionDomain input bubble).origin region ≠ bubble := by
  have survives :=
    (vacuousRegionDomain input bubble).origin_survives region
  exact (vacuousRegionDomain_survives input bubble _).1 survives

theorem VacuousElimTrace.parent_ne_bubble
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    trace.parent ≠ bubble := by
  intro equality
  have parent :
      (input.regions bubble).parent? = some trace.parent := by
    rw [trace.bubble_eq]
    rfl
  have notEncloses :=
    ConcreteElaboration.checked_direct_child_not_encloses_parent
      wellFormed parent
  apply notEncloses
  rw [equality]
  exact ConcreteDiagram.Encloses.refl input bubble

theorem VacuousElimTrace.parent_survives
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    (vacuousRegionDomain input bubble).survives trace.parent = true := by
  exact (vacuousRegionDomain_survives input bubble trace.parent).2
    (trace.parent_ne_bubble wellFormed)

theorem VacuousElimTrace.atom_binder_ne
    (trace : VacuousElimTrace input bubble raw)
    (node : Fin input.nodeCount)
    (owner binder : Fin input.regionCount)
    (node_eq : input.nodes node = .atom owner binder) :
    binder ≠ bubble := by
  intro equality
  subst binder
  have empty :
      (filterFin fun candidate =>
        match input.nodes candidate with
        | .atom _ candidateBinder => decide (candidateBinder = bubble)
        | _ => false) = [] :=
    List.isEmpty_iff.mp trace.bound_atoms_empty
  have member :
      node ∈ filterFin fun candidate =>
        match input.nodes candidate with
        | .atom _ candidateBinder => decide (candidateBinder = bubble)
        | _ => false := by
    rw [mem_filterFin, node_eq]
    simp
  rw [empty] at member
  exact List.not_mem_nil member

theorem vacuousElimRaw?_wireCount
    (hraw : vacuousElimRaw? input bubble = some raw) :
    raw.wireCount = input.wireCount := by
  unfold vacuousElimRaw? at hraw
  repeat' first | split at hraw <;> try contradiction
  dsimp only at hraw
  repeat' first | split at hraw <;> try contradiction
  exact promoteDiagramRaw?_wireCount hraw

def vacuousElimWireProvenance
    (hraw : vacuousElimRaw? input bubble = some raw) :
    WireProvenance input raw :=
  WireProvenance.byWireCount input raw
    (vacuousElimRaw?_wireCount hraw).symm

def vacuousElimInterfaceTransport
    (hraw : vacuousElimRaw? input bubble = some raw) :
    InterfaceTransport input raw :=
  InterfaceTransport.byWireCount input raw
    (vacuousElimRaw?_wireCount hraw).symm

def applyVacuousElim (input : CheckedDiagram signature)
    (bubble : Fin input.val.regionCount) :
    Except StepError (StepReceipt input) :=
  match hraw : vacuousElimRaw? input.val bubble with
  | none => .error .nonVacuousBinder
  | some raw =>
      match hcheck : checkWellFormed signature raw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (StepReceipt.ofChecked input raw
          (vacuousElimWireProvenance hraw)
          (vacuousElimInterfaceTransport hraw) result hcheck)

theorem applyVacuousElim_success_shape
    (happly : applyVacuousElim input bubble = .ok result) :
    ∃ raw, vacuousElimRaw? input.val bubble = some raw ∧
      result.result.val = raw := by
  unfold applyVacuousElim at happly
  split at happly <;> try contradiction
  rename_i raw hraw
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨raw, hraw, checkWellFormed_preserves_input hcheck⟩

theorem applyVacuousElim_realizes
    (happly : applyVacuousElim input bubble = .ok result) :
    ∃ raw, ∃ hraw : vacuousElimRaw? input.val bubble = some raw,
      result.Realizes raw (vacuousElimWireProvenance hraw)
        (vacuousElimInterfaceTransport hraw) := by
  unfold applyVacuousElim at happly
  split at happly <;> try contradiction
  rename_i raw hraw
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨raw, hraw, StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

end VisualProof.Rule
