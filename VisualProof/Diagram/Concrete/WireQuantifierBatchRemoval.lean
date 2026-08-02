import VisualProof.Diagram.Concrete.WellFormed
import VisualProof.Diagram.Concrete.Subgraph.Extract

namespace VisualProof

namespace ConcreteWireQuantifier

/-- Concrete construction failures owned below the rule-policy boundary. -/
inductive Error
  | expectedRelation (wire : Nat)
  | sameWire
  | signatureMismatch
  | invalidEndpointPartition
  | invalidSeverScope
  | emptyRelationSites
  | overlappingRemoval
  | invalidRemoval
  | removedRoot
  | removedScope
  | removedSite
  | removedFormal (wire : Nat)
  | relationSignatureMismatch
  | boundaryArityMismatch
  | boundarySignatureMismatch (position : Nat)
  | dyingWireParameter
  | nonAppliedEndpoint (node : Nat) (port : CPort)
  | invalidApplication (node : Nat)
  | invalidAttachment
  | wellFormed (error : WFError)
  deriving Repr, DecidableEq


namespace Internal

def retainedRegions
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId) :
    List source.val.RegionId :=
  source.val.regionsList.filter fun region =>
    decide (region ∉ removed)

def retainedNodes
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId) :
    List source.val.NodeId :=
  source.val.nodesList.filter fun node =>
    decide (node ∉ removed)

def retainedWires
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId) :
    List source.val.WireId :=
  source.val.wiresList.filter fun wire =>
    decide (wire ∉ removed)

/--
The complete structural evidence needed to densely remove a batch without a
repair fallback.  Only the executable checker below can construct this plan.
-/
structure BatchRemovalPlan
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) : Type where
  rootRetained :
    source.val.root ∈ retainedRegions source removedRegions
  parentRetained :
    ∀ target : Fin (retainedRegions source removedRegions).length,
      match source.val.regions
          ((retainedRegions source removedRegions).get target) with
      | .sheet => True
      | .cut parent =>
          parent ∈ retainedRegions source removedRegions
  nodeRegionRetained :
    ∀ target : Fin (retainedNodes source removedNodes).length,
      (source.val.nodes
          ((retainedNodes source removedNodes).get target)).region ∈
        retainedRegions source removedRegions
  wireScopeRetained :
    ∀ target : Fin (retainedWires source removedWires).length,
      (source.val.wires
          ((retainedWires source removedWires).get target)).scope ∈
        retainedRegions source removedRegions

def checkBatchRemovalPlan?
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) :
    Option
      (BatchRemovalPlan source removedRegions removedNodes removedWires) := by
  if rootRetained :
      source.val.root ∈ retainedRegions source removedRegions then
    if parentRetained :
        (retainedRegions source removedRegions).all (fun region =>
          match source.val.regions region with
          | .sheet => true
          | .cut parent =>
              decide (parent ∈ retainedRegions source removedRegions)) =
            true then
      if nodeRegionRetained :
          (retainedNodes source removedNodes).all (fun node =>
            decide (
              (source.val.nodes node).region ∈
                retainedRegions source removedRegions)) = true then
        if wireScopeRetained :
            (retainedWires source removedWires).all (fun wire =>
              decide (
                (source.val.wires wire).scope ∈
                  retainedRegions source removedRegions)) = true then
          exact some
            { rootRetained := rootRetained
              parentRetained := by
                intro target
                have accepted :=
                  (List.all_eq_true.mp parentRetained)
                    ((retainedRegions source removedRegions).get target)
                    (List.get_mem _ target)
                cases regionData :
                    source.val.regions
                      ((retainedRegions source removedRegions).get target) with
                | sheet => trivial
                | cut parent =>
                    rw [regionData] at accepted
                    exact of_decide_eq_true accepted
              nodeRegionRetained := by
                intro target
                exact of_decide_eq_true
                  ((List.all_eq_true.mp nodeRegionRetained)
                    ((retainedNodes source removedNodes).get target)
                    (List.get_mem _ target))
              wireScopeRetained := by
                intro target
                exact of_decide_eq_true
                  ((List.all_eq_true.mp wireScopeRetained)
                    ((retainedWires source removedWires).get target)
                    (List.get_mem _ target)) }
        else
          exact none
      else
        exact none
    else
      exact none
  else
    exact none

/-- Rechecking a checker-owned structural removal plan returns that plan. -/
theorem BatchRemovalPlan.checked
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires) :
    checkBatchRemovalPlan? source removedRegions removedNodes removedWires =
      some plan := by
  unfold checkBatchRemovalPlan?
  rw [dif_pos plan.rootRetained]
  have parents :
      (retainedRegions source removedRegions).all (fun region =>
        match source.val.regions region with
        | .sheet => true
        | .cut parent =>
            decide (parent ∈ retainedRegions source removedRegions)) =
        true := by
    apply List.all_eq_true.mpr
    intro region member
    let target := DenseList.index
      (retainedRegions source removedRegions) region member
    have regionExact :
        (retainedRegions source removedRegions).get target = region :=
      DenseList.get_index _ _ _
    have retained := plan.parentRetained target
    rw [regionExact] at retained
    cases regionData : source.val.regions region with
    | sheet => rfl
    | cut parent =>
        rw [regionData] at retained
        exact decide_eq_true retained
  rw [dif_pos parents]
  have nodes :
      (retainedNodes source removedNodes).all (fun node =>
        decide
          ((source.val.nodes node).region ∈
            retainedRegions source removedRegions)) = true := by
    apply List.all_eq_true.mpr
    intro node member
    let target := DenseList.index
      (retainedNodes source removedNodes) node member
    have nodeExact :
        (retainedNodes source removedNodes).get target = node :=
      DenseList.get_index _ _ _
    apply decide_eq_true
    rw [← nodeExact]
    exact plan.nodeRegionRetained target
  rw [dif_pos nodes]
  have wires :
      (retainedWires source removedWires).all (fun wire =>
        decide
          ((source.val.wires wire).scope ∈
            retainedRegions source removedRegions)) = true := by
    apply List.all_eq_true.mpr
    intro wire member
    let target := DenseList.index
      (retainedWires source removedWires) wire member
    have wireExact :
        (retainedWires source removedWires).get target = wire :=
      DenseList.get_index _ _ _
    apply decide_eq_true
    rw [← wireExact]
    exact plan.wireScopeRetained target
  rw [dif_pos wires]

/--
Removing no regions always admits the structural dense-removal plan.  Node
and wire deletion cannot invalidate the region-parent, node-region, or
wire-scope side of the plan because every source region is retained.
-/
theorem checkBatchRemovalPlan_noRegions
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) :
    ∃ plan,
      checkBatchRemovalPlan? source [] removedNodes removedWires = some plan := by
  have retained : retainedRegions source [] = source.val.regionsList := by
    simp [retainedRegions]
  unfold checkBatchRemovalPlan?
  simp only [retained]
  have root : source.val.root ∈ source.val.regionsList := by
    simp [ConcreteDiagram.regionsList]
  rw [dif_pos root]
  have parents :
      source.val.regionsList.all (fun region =>
        match source.val.regions region with
        | .sheet => true
        | .cut parent => decide (parent ∈ source.val.regionsList)) = true := by
    apply List.all_eq_true.mpr
    intro region member
    split <;> simp [ConcreteDiagram.regionsList,
      Data.Finite.mem_allFin]
  have nodes :
      (retainedNodes source removedNodes).all (fun node =>
        decide ((source.val.nodes node).region ∈ source.val.regionsList)) =
        true := by
    apply List.all_eq_true.mpr
    intro node member
    simp [ConcreteDiagram.regionsList, Data.Finite.mem_allFin]
  have wires :
      (retainedWires source removedWires).all (fun wire =>
        decide ((source.val.wires wire).scope ∈ source.val.regionsList)) =
        true := by
    apply List.all_eq_true.mpr
    intro wire member
    simp [ConcreteDiagram.regionsList, Data.Finite.mem_allFin]
  split
  · exact ⟨_, rfl⟩
  · rename_i rejected
    exact False.elim (rejected parents)

def retainedRegionIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId)
    (region : source.val.RegionId)
    (member : region ∈ retainedRegions source removed) :
    Fin (retainedRegions source removed).length :=
  DenseList.index (retainedRegions source removed) region member

def retainedNodeIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId)
    (node : source.val.NodeId)
    (member : node ∈ retainedNodes source removed) :
    Fin (retainedNodes source removed).length :=
  DenseList.index (retainedNodes source removed) node member

def retainedWireIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId)
    (wire : source.val.WireId)
    (member : wire ∈ retainedWires source removed) :
    Fin (retainedWires source removed).length :=
  DenseList.index (retainedWires source removed) wire member

def sourceRetainedRegion
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId)
    (region : Fin (retainedRegions source removed).length) :
    source.val.RegionId :=
  (retainedRegions source removed).get region

@[simp] theorem retainedRegions_nil
    (source : CheckedDiagram definitions) :
    retainedRegions source [] = source.val.regionsList := by
  simp [retainedRegions]

/--
When no region is removed, dense region allocation is a genuine equivalence
with the source carrier.  Node/wire-only rewrites use this receipt instead of
re-proving casts through the filtered region list.
-/
def noRegionRemovalEquiv
    (source : CheckedDiagram definitions) :
    Data.Finite.FiniteEquiv source.val.RegionId
      (Fin (retainedRegions source []).length) where
  toFun := fun region =>
    retainedRegionIndex source [] region (by
      rw [retainedRegions_nil]
      exact Data.Finite.mem_allFin region)
  invFun := sourceRetainedRegion source []
  left_inv := by
    intro region
    exact DenseList.get_index _ _ _
  right_inv := by
    intro region
    exact DenseList.index_get _ (by
      rw [retainedRegions_nil]
      exact Data.Finite.allFin_nodup source.val.regionCount) region

@[simp] theorem noRegionRemovalEquiv_sourceRetainedRegion
    (source : CheckedDiagram definitions)
    (region : Fin (retainedRegions source []).length) :
    noRegionRemovalEquiv source
        (sourceRetainedRegion source [] region) =
      region :=
  (noRegionRemovalEquiv source).right_inv region

@[simp] theorem sourceRetainedRegion_noRegionRemovalEquiv
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    sourceRetainedRegion source [] (noRegionRemovalEquiv source region) =
      region :=
  (noRegionRemovalEquiv source).left_inv region

def sourceRetainedNode
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId)
    (node : Fin (retainedNodes source removed).length) :
    source.val.NodeId :=
  (retainedNodes source removed).get node

def sourceRetainedWire
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId)
    (wire : Fin (retainedWires source removed).length) :
    source.val.WireId :=
  (retainedWires source removed).get wire

private theorem batchParentRetained
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (region : Fin (retainedRegions source removedRegions).length)
    (parent : source.val.RegionId)
    (regionData :
      source.val.regions
          (sourceRetainedRegion source removedRegions region) =
        .cut parent) :
    parent ∈ retainedRegions source removedRegions := by
  have retained := plan.parentRetained region
  have same :
      source.val.regions
          ((retainedRegions source removedRegions).get region) =
        .cut parent := by
    simpa [sourceRetainedRegion] using regionData
  rw [same] at retained
  exact retained

def batchRegionTable
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (region : Fin (retainedRegions source removedRegions).length) :
    CRegion (retainedRegions source removedRegions).length :=
  match regionData : source.val.regions
      (sourceRetainedRegion source removedRegions region) with
  | .sheet => .sheet
  | .cut parent =>
      .cut
        (retainedRegionIndex source removedRegions parent
          (batchParentRetained plan region parent regionData))

theorem batchRegionTable_retained_sheet
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source removedRegions removedNodes removedWires)
    (region : source.val.RegionId)
    (retained : region ∈ retainedRegions source removedRegions)
    (data : source.val.regions region = .sheet) :
    batchRegionTable plan
        (retainedRegionIndex source removedRegions region retained) =
      .sheet := by
  have sourceAt :
      sourceRetainedRegion source removedRegions
          (retainedRegionIndex source removedRegions region retained) = region :=
    DenseList.get_index _ _ _
  unfold batchRegionTable
  split
  · rfl
  · rename_i parent actual
    have impossible : source.val.regions region = .cut parent := by
      rw [← sourceAt]
      exact actual
    rw [data] at impossible
    contradiction

theorem batchRegionTable_retained_cut
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source removedRegions removedNodes removedWires)
    (region : source.val.RegionId)
    (retained : region ∈ retainedRegions source removedRegions)
    (parent : source.val.RegionId)
    (data : source.val.regions region = .cut parent)
    (parentRetained : parent ∈ retainedRegions source removedRegions) :
    batchRegionTable plan
        (retainedRegionIndex source removedRegions region retained) =
      .cut (retainedRegionIndex source removedRegions parent
        parentRetained) := by
  have sourceAt :
      sourceRetainedRegion source removedRegions
          (retainedRegionIndex source removedRegions region retained) = region :=
    DenseList.get_index _ _ _
  unfold batchRegionTable
  split
  · rename_i actual
    have impossible : source.val.regions region = .sheet := by
      rw [← sourceAt]
      exact actual
    rw [data] at impossible
    contradiction
  · rename_i actualParent actual
    have actualAt : source.val.regions region = .cut actualParent := by
      rw [← sourceAt]
      exact actual
    have parentExact : actualParent = parent :=
      CRegion.cut.inj (actualAt.symm.trans data)
    subst actualParent
    rfl

@[simp] theorem batchRegionTable_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (region : source.val.RegionId) :
    batchRegionTable plan (noRegionRemovalEquiv source region) =
      (source.val.regions region).rename
        (noRegionRemovalEquiv source) := by
  unfold batchRegionTable
  cases regionData : source.val.regions region with
  | sheet =>
      have retainedData :
          source.val.regions
              (sourceRetainedRegion source []
                (noRegionRemovalEquiv source region)) =
            .sheet := by
        rw [sourceRetainedRegion_noRegionRemovalEquiv]
        exact regionData
      simp only [CRegion.rename]
      split
      · rfl
      · rename_i parent impossible
        have contradiction : CRegion.cut parent = CRegion.sheet :=
          impossible.symm.trans retainedData
        contradiction
  | cut parent =>
      have retainedData :
          source.val.regions
              (sourceRetainedRegion source []
                (noRegionRemovalEquiv source region)) =
            .cut parent := by
        rw [sourceRetainedRegion_noRegionRemovalEquiv]
        exact regionData
      simp only [CRegion.rename]
      split
      · rename_i impossible
        have contradiction : CRegion.sheet = CRegion.cut parent :=
          impossible.symm.trans retainedData
        contradiction
      · rename_i actualParent actualData
        have parentExact : actualParent = parent :=
          CRegion.cut.inj (actualData.symm.trans retainedData)
        subst actualParent
        rfl

def batchNodeTable
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (node : Fin (retainedNodes source removedNodes).length) :
    CNode (retainedRegions source removedRegions).length definitions.length :=
  let sourceNode := sourceRetainedNode source removedNodes node
  let region :=
    retainedRegionIndex source removedRegions
      (source.val.nodes sourceNode).region
      (plan.nodeRegionRetained node)
  match source.val.nodes sourceNode with
  | .atom _ arguments => .atom region arguments
  | .ref _ definition arguments => .ref region definition arguments
  | .identity _ signature arity => .identity region signature arity

/-- Exact retained-node payload and transported region in a batch table. -/
theorem batchNodeTable_retained_data
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source removedRegions removedNodes removedWires)
    (target : Fin (retainedNodes source removedNodes).length) :
    batchNodeTable plan target =
      (source.val.nodes
        (sourceRetainedNode source removedNodes target)).relocate
        (retainedRegionIndex source removedRegions
          (source.val.nodes
            (sourceRetainedNode source removedNodes target)).region
          (plan.nodeRegionRetained target)) := by
  unfold batchNodeTable
  dsimp only
  let mapped := retainedRegionIndex source removedRegions
    (source.val.nodes
      (sourceRetainedNode source removedNodes target)).region
    (plan.nodeRegionRetained target)
  change
    (match source.val.nodes
        (sourceRetainedNode source removedNodes target) with
      | .atom _ args => .atom mapped args
      | .ref _ definition args => .ref mapped definition args
      | .identity _ sig arity => .identity mapped sig arity) =
      (source.val.nodes
        (sourceRetainedNode source removedNodes target)).relocate mapped
  clear_value mapped
  cases nodeData :
      source.val.nodes (sourceRetainedNode source removedNodes target) <;>
    simp [nodeData, CNode.relocate]

@[simp] theorem batchNodeTable_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (node : Fin (retainedNodes source removedNodes).length) :
    batchNodeTable plan node =
      (source.val.nodes
        (sourceRetainedNode source removedNodes node)).rename
          (noRegionRemovalEquiv source) := by
  unfold batchNodeTable
  cases data : source.val.nodes
      (sourceRetainedNode source removedNodes node) <;>
    simp [data, CNode.rename, noRegionRemovalEquiv]
  all_goals apply Fin.ext <;> rfl

def batchEndpoint?
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount) :
    Option (CEndpoint (retainedNodes source removedNodes).length) :=
  if retained : endpoint.node ∈ retainedNodes source removedNodes then
    some
      { node :=
          retainedNodeIndex source removedNodes endpoint.node retained
        port := endpoint.port }
  else
    none

def batchWireTable
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (wire : Fin (retainedWires source removedWires).length) :
    CWire
      (retainedRegions source removedRegions).length
      (retainedNodes source removedNodes).length :=
  let sourceWire := sourceRetainedWire source removedWires wire
  let data := source.val.wires sourceWire
  { sig := data.sig
    scope :=
      retainedRegionIndex source removedRegions data.scope
        (plan.wireScopeRetained wire)
    endpoints := data.endpoints.filterMap
      (batchEndpoint? source removedNodes) }

def batchRemovalCandidate
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires) :
    ConcreteDiagram definitions.length where
  regionCount := (retainedRegions source removedRegions).length
  nodeCount := (retainedNodes source removedNodes).length
  wireCount := (retainedWires source removedWires).length
  root :=
    retainedRegionIndex source removedRegions source.val.root
      plan.rootRetained
  regions := batchRegionTable plan
  nodes := batchNodeTable plan
  wires := batchWireTable plan

@[simp] theorem batchRemovalCandidate_regionCount_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires) :
    (batchRemovalCandidate plan).regionCount = source.val.regionCount := by
  simp [batchRemovalCandidate, ConcreteDiagram.regionsList,
    Data.Finite.allFin_eq_finRange, List.length_finRange]

@[simp] theorem batchRemovalCandidate_root_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires) :
    (batchRemovalCandidate plan).root =
      noRegionRemovalEquiv source source.val.root := by
  rfl

theorem batchRemovalCandidate_climb_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (steps : Nat)
    (region : source.val.RegionId) :
    (batchRemovalCandidate plan).climb steps
        (noRegionRemovalEquiv source region) =
      (source.val.climb steps region).map
        (noRegionRemovalEquiv source) := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps induction =>
      unfold ConcreteDiagram.climb
      simp only [batchRemovalCandidate]
      rw [batchRegionTable_noRegions]
      cases source.val.regions region with
      | sheet => rfl
      | cut parent => exact induction parent

theorem batchRemovalCandidate_encloses_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (outer inner : source.val.RegionId) :
    (batchRemovalCandidate plan).Encloses
        (noRegionRemovalEquiv source outer)
        (noRegionRemovalEquiv source inner) ↔
      source.val.Encloses outer inner := by
  have countExact := batchRemovalCandidate_regionCount_noRegions plan
  unfold ConcreteDiagram.Encloses
  constructor
  · intro accepted
    obtain ⟨steps, _member, climbed⟩ := List.any_eq_true.mp accepted
    have bound : steps.val < source.val.regionCount + 1 := by
      simpa [countExact] using steps.isLt
    let sourceSteps : Fin (source.val.regionCount + 1) :=
      ⟨steps.val, bound⟩
    apply List.any_eq_true.mpr
    refine ⟨sourceSteps, Data.Finite.mem_allFin sourceSteps, ?_⟩
    have mapped :=
      batchRemovalCandidate_climb_noRegions plan steps.val inner
    have exactMapped :
        (source.val.climb steps.val inner).map
            (noRegionRemovalEquiv source) =
          some (noRegionRemovalEquiv source outer) := by
      exact mapped.symm.trans (eq_of_beq climbed)
    cases sourceClimb : source.val.climb steps.val inner with
    | none => simp [sourceClimb] at exactMapped
    | some actual =>
        have actualExact : actual = outer :=
          (noRegionRemovalEquiv source).injective
            (Option.some.inj (by simpa [sourceClimb] using exactMapped))
        exact beq_iff_eq.mpr (by simpa [sourceSteps, sourceClimb, actualExact])
  · intro accepted
    obtain ⟨steps, _member, climbed⟩ := List.any_eq_true.mp accepted
    have bound :
        steps.val < (batchRemovalCandidate plan).regionCount + 1 := by
      simpa [countExact] using steps.isLt
    let targetSteps :
        Fin ((batchRemovalCandidate plan).regionCount + 1) :=
      ⟨steps.val, bound⟩
    apply List.any_eq_true.mpr
    refine ⟨targetSteps, Data.Finite.mem_allFin targetSteps, ?_⟩
    rw [batchRemovalCandidate_climb_noRegions]
    have sourceExact :
        source.val.climb steps.val inner = some outer :=
      eq_of_beq climbed
    rw [sourceExact]
    exact beq_self_eq_true _

theorem batchRemovalCandidate_rootIsSheet_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires) :
    (batchRemovalCandidate plan).RootIsSheet := by
  unfold ConcreteDiagram.RootIsSheet
  rw [batchRemovalCandidate_root_noRegions]
  change batchRegionTable plan
      (noRegionRemovalEquiv source source.val.root) = .sheet
  rw [batchRegionTable_noRegions, source.property.root_is_sheet]
  rfl

theorem batchRemovalCandidate_onlyRootIsSheet_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires) :
    (batchRemovalCandidate plan).OnlyRootIsSheet := by
  unfold ConcreteDiagram.OnlyRootIsSheet
  apply List.all_eq_true.mpr
  intro region regionMember
  let original := (noRegionRemovalEquiv source).symm region
  have regionExact : noRegionRemovalEquiv source original = region :=
    (noRegionRemovalEquiv source).right_inv region
  apply decide_eq_true
  intro sheet
  have sheetAtOriginal :
      (batchRemovalCandidate plan).regions
          (noRegionRemovalEquiv source original) = .sheet := by
    rw [regionExact]
    exact sheet
  have renamedSheet :
      (source.val.regions original).rename
          (noRegionRemovalEquiv source) = .sheet := by
    rw [← batchRegionTable_noRegions plan original]
    exact sheetAtOriginal
  have sourceSheet : source.val.regions original = .sheet := by
    cases data : source.val.regions original with
    | sheet => rfl
    | cut parent => simp [data, CRegion.rename] at renamedSheet
  have sourceCheck :=
    (List.all_eq_true.mp source.property.only_root_is_sheet)
      original (Data.Finite.mem_allFin original)
  have originalRoot : original = source.val.root := by
    exact (of_decide_eq_true sourceCheck) sourceSheet
  have mappedRoot :
      noRegionRemovalEquiv source original =
        noRegionRemovalEquiv source source.val.root := by
    rw [originalRoot]
  have targetRoot :
      noRegionRemovalEquiv source source.val.root =
        (batchRemovalCandidate plan).root :=
    (batchRemovalCandidate_root_noRegions plan).symm
  exact regionExact.symm.trans (mappedRoot.trans targetRoot)

theorem batchRemovalCandidate_allRegionsReachRoot_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires) :
    (batchRemovalCandidate plan).AllRegionsReachRoot := by
  unfold ConcreteDiagram.AllRegionsReachRoot
  apply List.all_eq_true.mpr
  intro region regionMember
  let original := (noRegionRemovalEquiv source).symm region
  have regionExact : noRegionRemovalEquiv source original = region :=
    (noRegionRemovalEquiv source).right_inv region
  apply decide_eq_true
  rw [← regionExact]
  rw [batchRemovalCandidate_root_noRegions,
    batchRemovalCandidate_encloses_noRegions]
  exact of_decide_eq_true
    ((List.all_eq_true.mp source.property.all_regions_reach_root)
      original (Data.Finite.mem_allFin original))

private inductive NodePayload (definitionCount : Nat)
  | atom (arguments : List Sig)
  | ref (definition : Fin definitionCount) (arguments : List Sig)
  | identity (signature : Sig) (arity : Nat)

private def nodePayload :
    CNode regionCount definitionCount → NodePayload definitionCount
  | .atom _ arguments => .atom arguments
  | .ref _ definition arguments => .ref definition arguments
  | .identity _ signature arity => .identity signature arity

private theorem nodePayload_remapRegion
    (region : Fin targetRegionCount)
    (node : CNode sourceRegionCount definitionCount) :
    nodePayload
        (match node with
        | .atom _ arguments => .atom region arguments
        | .ref _ definition arguments => .ref region definition arguments
        | .identity _ signature arity =>
            .identity region signature arity) =
      nodePayload node := by
  cases node <;> rfl

private theorem nodePayload_batchNodeTable
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (node : Fin (retainedNodes source removedNodes).length) :
    nodePayload (batchNodeTable plan node) =
      nodePayload
        (source.val.nodes (sourceRetainedNode source removedNodes node)) := by
  let sourceNode := sourceRetainedNode source removedNodes node
  let sourceData := source.val.nodes sourceNode
  have retained : sourceData.region ∈
      retainedRegions source removedRegions := by
    exact plan.nodeRegionRetained node
  let region :=
    retainedRegionIndex source removedRegions sourceData.region retained
  change
    nodePayload
        (match sourceData with
        | .atom _ arguments => .atom region arguments
        | .ref _ definition arguments => .ref region definition arguments
        | .identity _ signature arity =>
            .identity region signature arity) =
      nodePayload sourceData
  cases sourceData <;> rfl

private def referenceMatchesPayload
    (definitions : List (List Sig)) :
    NodePayload definitions.length → Bool
  | .ref definition arguments => arguments == definitions.get definition
  | _ => true

private def identityHasArityPayload :
    NodePayload definitionCount → Bool
  | .identity _ arity => decide (2 ≤ arity)
  | _ => true

private theorem referenceMatch_eq_payload
    (definitions : List (List Sig))
    (node : CNode regionCount definitions.length) :
    (match node with
      | .ref _ definition arguments =>
          arguments == definitions.get definition
      | _ => true) =
      referenceMatchesPayload definitions (nodePayload node) := by
  cases node <;> rfl

private theorem identityArity_eq_payload
    (node : CNode regionCount definitionCount) :
    (match node with
      | .identity _ _ arity => decide (2 ≤ arity)
      | _ => true) =
      identityHasArityPayload (nodePayload node) := by
  cases node <;> rfl

/-- Dense node removal preserves chronological reference signatures. -/
theorem batchRemovalCandidate_referencesMatch
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires) :
    (batchRemovalCandidate plan).ReferencesMatch definitions := by
  unfold ConcreteDiagram.ReferencesMatch
  apply List.all_eq_true.mpr
  intro node _member
  let original := sourceRetainedNode source removedNodes node
  have sourceChecked :=
    (List.all_eq_true.mp source.property.references_match)
      original (Data.Finite.mem_allFin original)
  dsimp [original] at sourceChecked
  have sourcePayloadChecked :
      referenceMatchesPayload definitions
          (nodePayload
            (source.val.nodes
              (sourceRetainedNode source removedNodes node))) =
        true := by
    cases sourceData :
        source.val.nodes (sourceRetainedNode source removedNodes node) <;>
      simp_all [referenceMatchesPayload, nodePayload]
  have basePayloadChecked :
      referenceMatchesPayload definitions
          (nodePayload (batchNodeTable plan node)) = true := by
    rw [nodePayload_batchNodeTable]
    exact sourcePayloadChecked
  simp only [batchRemovalCandidate]
  cases baseData : batchNodeTable plan node <;>
    simp_all [referenceMatchesPayload, nodePayload]

/-- Dense node removal preserves the minimum arity of retained identities. -/
theorem batchRemovalCandidate_identitiesHaveArity
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires) :
    (batchRemovalCandidate plan).IdentitiesHaveArity := by
  unfold ConcreteDiagram.IdentitiesHaveArity
  apply List.all_eq_true.mpr
  intro node _member
  let original := sourceRetainedNode source removedNodes node
  have sourceChecked :=
    (List.all_eq_true.mp source.property.identities_have_arity)
      original (Data.Finite.mem_allFin original)
  dsimp [original] at sourceChecked
  have sourcePayloadChecked :
      identityHasArityPayload
          (nodePayload
            (source.val.nodes
              (sourceRetainedNode source removedNodes node))) =
        true := by
    cases sourceData :
        source.val.nodes (sourceRetainedNode source removedNodes node) <;>
      simp_all [identityHasArityPayload, nodePayload]
  have basePayloadChecked :
      identityHasArityPayload (nodePayload (batchNodeTable plan node)) =
        true := by
    rw [nodePayload_batchNodeTable]
    exact sourcePayloadChecked
  simp only [batchRemovalCandidate]
  cases baseData : batchNodeTable plan node <;>
    simp_all [identityHasArityPayload, nodePayload]

private theorem retainedNodes_nodup
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId) :
    (retainedNodes source removedNodes).Nodup := by
  unfold retainedNodes
  exact (Data.Finite.allFin_nodup source.val.nodeCount).filter _

private theorem retainedWires_nodup
    (source : CheckedDiagram definitions)
    (removedWires : List source.val.WireId) :
    (retainedWires source removedWires).Nodup := by
  unfold retainedWires
  exact (Data.Finite.allFin_nodup source.val.wireCount).filter _

@[simp] theorem sourceRetainedNode_retainedNodeIndex
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (node : source.val.NodeId)
    (retained : node ∈ retainedNodes source removedNodes) :
    sourceRetainedNode source removedNodes
        (retainedNodeIndex source removedNodes node retained) =
      node :=
  DenseList.get_index _ _ _

@[simp] theorem retainedNodeIndex_sourceRetainedNode
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (node : Fin (retainedNodes source removedNodes).length) :
    retainedNodeIndex source removedNodes
        (sourceRetainedNode source removedNodes node)
        (List.get_mem _ node) =
      node :=
  DenseList.index_get _ (retainedNodes_nodup source removedNodes) node

@[simp] theorem sourceRetainedWire_retainedWireIndex
    (source : CheckedDiagram definitions)
    (removedWires : List source.val.WireId)
    (wire : source.val.WireId)
    (retained : wire ∈ retainedWires source removedWires) :
    sourceRetainedWire source removedWires
        (retainedWireIndex source removedWires wire retained) =
      wire :=
  DenseList.get_index _ _ _

@[simp] theorem retainedWireIndex_sourceRetainedWire
    (source : CheckedDiagram definitions)
    (removedWires : List source.val.WireId)
    (wire : Fin (retainedWires source removedWires).length) :
    retainedWireIndex source removedWires
        (sourceRetainedWire source removedWires wire)
        (List.get_mem _ wire) =
      wire :=
  DenseList.index_get _ (retainedWires_nodup source removedWires) wire

/-- The source endpoint represented by one dense retained endpoint. -/
def sourceRetainedEndpoint
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (endpoint : CEndpoint (retainedNodes source removedNodes).length) :
    CEndpoint source.val.nodeCount :=
  ⟨sourceRetainedNode source removedNodes endpoint.node, endpoint.port⟩

@[simp] theorem batchEndpoint_sourceRetainedEndpoint
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (endpoint : CEndpoint (retainedNodes source removedNodes).length) :
    batchEndpoint? source removedNodes
        (sourceRetainedEndpoint source removedNodes endpoint) =
      some endpoint := by
  unfold batchEndpoint? sourceRetainedEndpoint
  simp only
  have retained :
      sourceRetainedNode source removedNodes endpoint.node ∈
        retainedNodes source removedNodes :=
    List.get_mem _ endpoint.node
  rw [dif_pos retained]
  apply congrArg some
  cases endpoint with
  | mk node port =>
      congr
      exact retainedNodeIndex_sourceRetainedNode source removedNodes node

/-- Successful endpoint densification has the unique retained source origin. -/
theorem sourceRetainedEndpoint_of_batchEndpoint
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (sourceEndpoint : CEndpoint source.val.nodeCount)
    (targetEndpoint : CEndpoint (retainedNodes source removedNodes).length)
    (mapped :
      batchEndpoint? source removedNodes sourceEndpoint =
        some targetEndpoint) :
    sourceRetainedEndpoint source removedNodes targetEndpoint =
      sourceEndpoint := by
  unfold batchEndpoint? at mapped
  split at mapped
  · rename_i retained
    have exactEndpoint := Option.some.inj mapped
    cases sourceEndpoint with
    | mk sourceNode sourcePort =>
        cases targetEndpoint with
        | mk targetNode targetPort =>
            simp only [sourceRetainedEndpoint] at exactEndpoint ⊢
            have nodeExact :
                targetNode =
                  retainedNodeIndex source removedNodes sourceNode retained :=
              congrArg CEndpoint.node exactEndpoint.symm
            have portExact : targetPort = sourcePort :=
              congrArg CEndpoint.port exactEndpoint.symm
            subst targetNode
            subst targetPort
            simp
  · contradiction

/-- Dense batch incidence is exactly filtered source incidence. -/
theorem batchRemovalCandidate_endpoint_iff
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (wire : (batchRemovalCandidate plan).WireId)
    (endpoint : CEndpoint (batchRemovalCandidate plan).nodeCount) :
    endpoint ∈ ((batchRemovalCandidate plan).wires wire).endpoints ↔
      sourceRetainedEndpoint source removedNodes endpoint ∈
        (source.val.wires
          (sourceRetainedWire source removedWires wire)).endpoints := by
  change endpoint ∈
      (source.val.wires
        (sourceRetainedWire source removedWires wire)).endpoints.filterMap
          (batchEndpoint? source removedNodes) ↔ _
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨sourceEndpoint, sourceMember, mapped⟩
    rw [sourceRetainedEndpoint_of_batchEndpoint source removedNodes
      sourceEndpoint endpoint mapped]
    exact sourceMember
  · intro sourceMember
    apply List.mem_filterMap.mpr
    exact
      ⟨sourceRetainedEndpoint source removedNodes endpoint,
        sourceMember,
        batchEndpoint_sourceRetainedEndpoint source removedNodes endpoint⟩

@[simp] theorem batchRemovalCandidate_requiredPorts
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (node : (batchRemovalCandidate plan).NodeId) :
    (batchRemovalCandidate plan).requiredPorts node =
      source.val.requiredPorts
        (sourceRetainedNode source removedNodes node) := by
  unfold ConcreteDiagram.requiredPorts
  rw [show (batchRemovalCandidate plan).nodes node = batchNodeTable plan node by rfl]
  have payload := nodePayload_batchNodeTable plan node
  cases targetData : batchNodeTable plan node <;>
    cases sourceData :
      source.val.nodes (sourceRetainedNode source removedNodes node) <;>
    simp_all [ConcreteDiagram.requiredPorts, nodePayload]

@[simp] theorem batchRemovalCandidate_wire_signature
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source removedRegions removedNodes removedWires)
    (wire : (batchRemovalCandidate plan).WireId) :
    ((batchRemovalCandidate plan).wires wire).sig =
      (source.val.wires
        (sourceRetainedWire source removedWires wire)).sig :=
  rfl

@[simp] theorem batchRemovalCandidate_wire_scope_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (wire : (batchRemovalCandidate plan).WireId) :
    ((batchRemovalCandidate plan).wires wire).scope =
      noRegionRemovalEquiv source
        (source.val.wires
          (sourceRetainedWire source removedWires wire)).scope := by
  change
    retainedRegionIndex source []
        (source.val.wires
          (sourceRetainedWire source removedWires wire)).scope
        (plan.wireScopeRetained wire) = _
  apply Fin.ext
  rfl

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

private theorem flatMap_get_allFin
    (values : List α) (function : α → List β) :
    (Data.Finite.allFin values.length).flatMap
        (fun index => function (values.get index)) =
      values.flatMap function := by
  rw [← List.flatMap_map]
  rw [map_get_allFin]

private theorem filter_flatMap_eq_flatMap_of_removed_empty
    [DecidableEq α]
    (values removed : List α) (function : α → List β)
    (removedEmpty : ∀ value, value ∈ removed → function value = []) :
    (values.filter fun value => decide (value ∉ removed)).flatMap function =
      values.flatMap function := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [decide_not] at induction ⊢
      by_cases removedHead : head ∈ removed
      · simp [removedHead, removedEmpty head removedHead, induction]
      · simp [removedHead, induction]

private theorem map_self (values : List α) :
    values.map (fun value => value) = values := by
  exact List.map_id values

private theorem batchEndpoint_filterMap_removed_eq_nil
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes)
    (wire : source.val.WireId)
    (removed : wire ∈ removedWires) :
    (source.val.wires wire).endpoints.filterMap
        (batchEndpoint? source removedNodes) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro endpoint incident
  unfold batchEndpoint?
  rw [dif_neg]
  intro retained
  have notRemoved : endpoint.node ∉ removedNodes :=
    of_decide_eq_true (List.mem_filter.mp retained).2
  exact notRemoved (exhausted wire removed endpoint incident)

private theorem batchRemovalCandidate_endpointValues
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes) :
    ((batchRemovalCandidate plan).endpointOccurrences.map Prod.snd) =
      (source.val.endpointOccurrences.map Prod.snd).filterMap
        (batchEndpoint? source removedNodes) := by
  simp only [ConcreteDiagram.endpointOccurrences, List.map_flatMap,
    List.map_map, Function.comp_def]
  simp only [map_self]
  change
    (Data.Finite.allFin (retainedWires source removedWires).length).flatMap
        (fun targetWire =>
          (source.val.wires
            ((retainedWires source removedWires).get targetWire)).endpoints.filterMap
              (batchEndpoint? source removedNodes)) =
      (source.val.wiresList.flatMap fun wire =>
        (source.val.wires wire).endpoints).filterMap
          (batchEndpoint? source removedNodes)
  rw [flatMap_get_allFin
    (retainedWires source removedWires)
    (fun wire =>
      (source.val.wires wire).endpoints.filterMap
        (batchEndpoint? source removedNodes))]
  rw [List.filterMap_flatMap]
  unfold retainedWires
  apply filter_flatMap_eq_flatMap_of_removed_empty
  intro wire removed
  exact batchEndpoint_filterMap_removed_eq_nil source removedNodes
    removedWires exhausted wire removed

private theorem eraseDups_length_le
    [BEq α] [LawfulBEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.succ_le_succ_iff]
      exact Nat.le_trans
        (eraseDups_length_le
          (tail.filter fun value => !value == head))
        (List.length_filter_le _ tail)
termination_by values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem nodup_of_eraseDups_length_eq
    [BEq α] [LawfulBEq α] (values : List α)
    (sameLength : values.eraseDups.length = values.length) :
    values.Nodup := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons] at sameLength
      simp only [List.length_cons, Nat.succ.injEq] at sameLength
      let retained := tail.filter fun value => !value == head
      have retainedLength : retained.length = tail.length := by
        apply Nat.le_antisymm
        · exact List.length_filter_le _ tail
        · rw [← sameLength]
          exact eraseDups_length_le retained
      have retainedEquality : retained = tail :=
        List.Sublist.eq_of_length List.filter_sublist retainedLength
      rw [List.nodup_cons]
      constructor
      · intro member
        have accepted : (!head == head) = true := by
          have : head ∈ retained := by
            rw [retainedEquality]
            exact member
          exact (List.mem_filter.mp this).2
        simp at accepted
      · apply nodup_of_eraseDups_length_eq tail
        simpa [retained, retainedEquality] using sameLength
termination_by values.length
decreasing_by simp_wf

private theorem eraseDups_eq_self_of_nodup
    [BEq α] [LawfulBEq α] (values : List α)
    (nodup : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      rw [List.eraseDups_cons]
      have filterEquality :
          tail.filter (fun value => !value == head) = tail := by
        rw [List.filter_eq_self]
        intro value member
        have different : value ≠ head :=
          fun equality => nodup.1 (equality ▸ member)
        simp [different]
      rw [filterEquality]
      rw [induction nodup.2]

private theorem source_endpointValues_nodup
    (source : CheckedDiagram definitions) :
    (source.val.endpointOccurrences.map Prod.snd).Nodup := by
  apply nodup_of_eraseDups_length_eq
  have noDuplicates := source.property.no_duplicate_endpoints
  unfold ConcreteDiagram.NoDuplicateEndpoints at noDuplicates
  simpa using noDuplicates

private theorem batchRemovalCandidate_endpointValues_nodup
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes) :
    ((batchRemovalCandidate plan).endpointOccurrences.map Prod.snd).Nodup := by
  rw [batchRemovalCandidate_endpointValues plan exhausted]
  rw [List.nodup_iff_pairwise_ne]
  exact
    (source_endpointValues_nodup source).filterMap
      (batchEndpoint? source removedNodes)
      (by
        intro left right different
        intro leftTarget leftMapped rightTarget rightMapped
        intro targetEquality
        apply different
        have leftExact :=
          sourceRetainedEndpoint_of_batchEndpoint source removedNodes
            left leftTarget leftMapped
        have rightExact :=
          sourceRetainedEndpoint_of_batchEndpoint source removedNodes
            right rightTarget rightMapped
        exact leftExact.symm.trans
          ((congrArg (sourceRetainedEndpoint source removedNodes)
            targetEquality).trans rightExact))

private theorem batchRemovalCandidate_no_duplicate_endpoints
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes) :
    (batchRemovalCandidate plan).NoDuplicateEndpoints := by
  unfold ConcreteDiagram.NoDuplicateEndpoints
  rw [eraseDups_eq_self_of_nodup _
    (batchRemovalCandidate_endpointValues_nodup plan exhausted)]
  exact List.length_map _

private theorem occurrence_incident
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId)
    (endpoint : CEndpoint diagram.nodeCount)
    (occurs : (wire, endpoint) ∈ diagram.endpointOccurrences) :
    endpoint ∈ (diagram.wires wire).endpoints := by
  simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap] at occurs
  rcases occurs with ⟨candidate, _, member⟩
  simp only [List.mem_map] at member
  rcases member with ⟨candidateEndpoint, incident, equality⟩
  cases equality
  exact incident

private theorem incident_occurrence
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId)
    (endpoint : CEndpoint diagram.nodeCount)
    (incident : endpoint ∈ (diagram.wires wire).endpoints) :
    (wire, endpoint) ∈ diagram.endpointOccurrences := by
  simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
  refine ⟨wire, Data.Finite.mem_allFin wire, ?_⟩
  exact List.mem_map.mpr ⟨endpoint, incident, rfl⟩

private theorem sourceRetainedNode_not_removed
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (node : Fin (retainedNodes source removedNodes).length) :
    sourceRetainedNode source removedNodes node ∉ removedNodes := by
  have member := List.get_mem (retainedNodes source removedNodes) node
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem batchRemovalCandidate_required_source_owner
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes)
    (node : (batchRemovalCandidate plan).NodeId)
    (port : CPort)
    (required : port ∈ (batchRemovalCandidate plan).requiredPorts node) :
    ∃ (sourceWire : source.val.WireId)
      (retained : sourceWire ∈ retainedWires source removedWires),
      source.val.endpointOwner?
          ⟨sourceRetainedNode source removedNodes node, port⟩ =
        some sourceWire := by
  have sourceRequired :
      port ∈ source.val.requiredPorts
        (sourceRetainedNode source removedNodes node) := by
    rw [← batchRemovalCandidate_requiredPorts plan node]
    exact required
  obtain ⟨sourceWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions source.val
      source.property (sourceRetainedNode source removedNodes node) port
      sourceRequired
  have notRemoved : sourceWire ∉ removedWires := by
    intro removed
    have incident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceRetainedNode source removedNodes node, port⟩ sourceWire
      sourceOwner
    exact sourceRetainedNode_not_removed source removedNodes node
      (exhausted sourceWire removed _ incident)
  have retained : sourceWire ∈ retainedWires source removedWires := by
    unfold retainedWires
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin sourceWire,
      decide_eq_true notRemoved⟩
  exact ⟨sourceWire, retained, sourceOwner⟩

private theorem batchRemovalCandidate_required_incident
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes)
    (node : (batchRemovalCandidate plan).NodeId)
    (port : CPort)
    (required : port ∈ (batchRemovalCandidate plan).requiredPorts node) :
    ∃ wire,
      (⟨node, port⟩ : CEndpoint (batchRemovalCandidate plan).nodeCount) ∈
        ((batchRemovalCandidate plan).wires wire).endpoints := by
  obtain ⟨sourceWire, retained, sourceOwner⟩ :=
    batchRemovalCandidate_required_source_owner plan exhausted node port
      required
  let targetWire :=
    retainedWireIndex source removedWires sourceWire retained
  refine ⟨targetWire, ?_⟩
  apply (batchRemovalCandidate_endpoint_iff plan targetWire
    ⟨node, port⟩).mpr
  have incident := ConcreteDiagram.endpointOwner?_incident source.val
    ⟨sourceRetainedNode source removedNodes node, port⟩ sourceWire
    sourceOwner
  have wireExact :
      sourceRetainedWire source removedWires targetWire = sourceWire := by
    unfold targetWire sourceRetainedWire retainedWireIndex
    rw [DenseList.get_index]
  rw [wireExact]
  exact incident

private theorem batchRemovalCandidate_ports_exist
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires) :
    (batchRemovalCandidate plan).PortsExist := by
  unfold ConcreteDiagram.PortsExist
  apply List.all_eq_true.mpr
  rintro ⟨wire, endpoint⟩ occurrence
  have targetIncident := occurrence_incident
    (batchRemovalCandidate plan) wire endpoint occurrence
  have sourceIncident :=
    (batchRemovalCandidate_endpoint_iff plan wire endpoint).mp
      targetIncident
  have sourceRequired := ConcreteDiagram.incident_port_required definitions
    source.val source.property
    (sourceRetainedWire source removedWires wire)
    (sourceRetainedEndpoint source removedNodes endpoint) sourceIncident
  apply decide_eq_true
  rw [batchRemovalCandidate_requiredPorts]
  exact sourceRequired

private theorem batchRemovalCandidate_ports_covered_exactly_once
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes) :
    (batchRemovalCandidate plan).PortsCoveredExactlyOnce := by
  unfold ConcreteDiagram.PortsCoveredExactlyOnce
  apply List.all_eq_true.mpr
  intro node _
  apply List.all_eq_true.mpr
  intro port required
  obtain ⟨wire, incident⟩ :=
    batchRemovalCandidate_required_incident plan exhausted node port required
  let endpoint : CEndpoint (batchRemovalCandidate plan).nodeCount :=
    ⟨node, port⟩
  have occurrence :
      (wire, endpoint) ∈ (batchRemovalCandidate plan).endpointOccurrences :=
    incident_occurrence (batchRemovalCandidate plan) wire endpoint incident
  have endpointMember :
      endpoint ∈
        (batchRemovalCandidate plan).endpointOccurrences.map Prod.snd :=
    List.mem_map.mpr ⟨(wire, endpoint), occurrence, rfl⟩
  have counted :=
    (batchRemovalCandidate_endpointValues_nodup plan exhausted).count
      (a := endpoint)
  rw [if_pos endpointMember] at counted
  rw [List.count_eq_length_filter] at counted
  rw [List.filter_map] at counted
  simp only [List.length_map] at counted
  have countOne :
      ((batchRemovalCandidate plan).endpointOccurrences.filter
        fun occurrence => occurrence.2 == endpoint).length = 1 :=
    counted
  have ownerSome :
      ((batchRemovalCandidate plan).endpointOwner? endpoint).isSome = true := by
    unfold ConcreteDiagram.endpointOwner?
    simp only [Option.isSome_map]
    rw [List.find?_isSome]
    exact ⟨(wire, endpoint), occurrence, beq_self_eq_true _⟩
  rw [Bool.and_eq_true]
  constructor
  · apply beq_iff_eq.mpr
    exact countOne
  · exact ownerSome

private theorem eq_of_filter_length_one_of_mem
    {values : List α} {predicate : α → Bool} {left right : α}
    (leftMember : left ∈ values) (rightMember : right ∈ values)
    (leftAccepted : predicate left = true)
    (rightAccepted : predicate right = true)
    (one : (values.filter predicate).length = 1) :
    left = right := by
  have leftFiltered : left ∈ values.filter predicate := by
    exact List.mem_filter.mpr ⟨leftMember, leftAccepted⟩
  have rightFiltered : right ∈ values.filter predicate := by
    exact List.mem_filter.mpr ⟨rightMember, rightAccepted⟩
  cases filtered : values.filter predicate with
  | nil => simp [filtered] at leftFiltered
  | cons head tail =>
      rw [filtered] at one leftFiltered rightFiltered
      have tailEmpty : tail = [] := by
        have : tail.length = 0 := by simpa using one
        exact List.length_eq_zero_iff.mp this
      subst tail
      simp only [List.mem_cons, List.not_mem_nil, or_false] at leftFiltered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at rightFiltered
      exact leftFiltered.trans rightFiltered.symm

private theorem endpointOwner?_eq_of_covered_incident
    (diagram : ConcreteDiagram definitionCount)
    (covered : diagram.PortsCoveredExactlyOnce)
    (node : diagram.NodeId) (port : CPort)
    (required : port ∈ diagram.requiredPorts node)
    (wire : diagram.WireId)
    (incident : (⟨node, port⟩ : CEndpoint diagram.nodeCount) ∈
      (diagram.wires wire).endpoints) :
    diagram.endpointOwner? ⟨node, port⟩ = some wire := by
  have nodeCheck := (List.all_eq_true.mp covered) node
    (Data.Finite.mem_allFin node)
  have portCheck := (List.all_eq_true.mp nodeCheck) port required
  rw [Bool.and_eq_true] at portCheck
  obtain ⟨owner, ownerEquation⟩ :=
    Option.isSome_iff_exists.mp portCheck.2
  have ownerOccurrence := ConcreteDiagram.endpointOwner?_occurs diagram
    ⟨node, port⟩ owner ownerEquation
  have wireOccurrence := incident_occurrence diagram wire ⟨node, port⟩
    incident
  have one :
      (diagram.endpointOccurrences.filter fun occurrence =>
        occurrence.2 ==
          (⟨node, port⟩ : CEndpoint diagram.nodeCount)).length = 1 := by
    exact eq_of_beq portCheck.1
  have pairEquality :
      (owner, (⟨node, port⟩ : CEndpoint diagram.nodeCount)) =
        (wire, ⟨node, port⟩) := by
    apply eq_of_filter_length_one_of_mem
      (predicate := fun occurrence :
        diagram.WireId × CEndpoint diagram.nodeCount =>
          occurrence.2 ==
            (⟨node, port⟩ : CEndpoint diagram.nodeCount))
      ownerOccurrence wireOccurrence
    · exact beq_self_eq_true _
    · exact beq_self_eq_true _
    · exact one
  have ownerEquality : owner = wire := congrArg Prod.fst pairEquality
  simpa [ownerEquality] using ownerEquation

private def portSignature? :
    CNode regionCount definitionCount → CPort → Option Sig
  | .atom _ arguments, .head => some (.rel arguments)
  | .atom _ arguments, .arg index => arguments[index]?
  | .ref _ _ arguments, .arg index => arguments[index]?
  | .identity _ signature arity, .identity index =>
      if index < arity then some signature else none
  | _, _ => none

private theorem portSignature?_some_required
    (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId)
    (port : CPort) (signature : Sig)
    (exact : portSignature? (diagram.nodes node) port = some signature) :
    port ∈ diagram.requiredPorts node := by
  cases nodeData : diagram.nodes node <;> cases port <;>
    simp [ConcreteDiagram.requiredPorts, nodeData, portSignature?] at exact ⊢
  all_goals
    try
      split at exact
      · simp_all
      · contradiction
  all_goals
    try
      rename_i arguments index
      cases item : arguments[index]? <;> simp [item] at exact
      exact List.getElem?_eq_some_iff.mp item |>.1
  all_goals simp_all

private theorem batchRemovalCandidate_portSignature
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (node : (batchRemovalCandidate plan).NodeId)
    (port : CPort) :
    portSignature? ((batchRemovalCandidate plan).nodes node) port =
      portSignature?
        (source.val.nodes (sourceRetainedNode source removedNodes node)) port := by
  rw [show (batchRemovalCandidate plan).nodes node = batchNodeTable plan node by rfl]
  have payload := nodePayload_batchNodeTable plan node
  cases targetData : batchNodeTable plan node <;>
    cases sourceData :
      source.val.nodes (sourceRetainedNode source removedNodes node) <;>
    cases port <;> simp_all [portSignature?, nodePayload]

private theorem checked_port_signature
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (port : CPort)
    (sourceWire : source.val.WireId)
    (owner : source.val.endpointOwner? ⟨node, port⟩ = some sourceWire)
    (signature : Sig)
    (intrinsic : portSignature? (source.val.nodes node) port = some signature) :
    (source.val.wires sourceWire).sig = signature := by
  cases nodeData : source.val.nodes node with
  | atom region arguments =>
      rw [nodeData] at intrinsic
      cases port with
      | head =>
          have checked :=
            (List.all_eq_true.mp source.property.atom_ports_typed)
              node (Data.Finite.mem_allFin node)
          rw [nodeData, owner, Bool.and_eq_true] at checked
          exact (eq_of_beq checked.1).trans
            (Option.some.inj (by simpa [portSignature?] using intrinsic))
      | arg index =>
          cases argument : arguments[index]? with
          | none => simp [portSignature?, nodeData, argument] at intrinsic
          | some expected =>
              have expectedExact : expected = signature :=
                Option.some.inj (by simpa [portSignature?, argument]
                  using intrinsic)
              have bound : index < arguments.length :=
                List.getElem?_eq_some_iff.mp argument |>.1
              have checked :=
                (List.all_eq_true.mp source.property.atom_ports_typed)
                  node (Data.Finite.mem_allFin node)
              rw [nodeData, Bool.and_eq_true] at checked
              have position := (List.all_eq_true.mp checked.2)
                index (by simpa using bound)
              rw [owner, argument] at position
              exact (eq_of_beq position).trans expectedExact
      | identity index => simp [portSignature?, nodeData] at intrinsic
  | ref region definition arguments =>
      rw [nodeData] at intrinsic
      cases port with
      | head => simp [portSignature?, nodeData] at intrinsic
      | arg index =>
          cases argument : arguments[index]? with
          | none => simp [portSignature?, nodeData, argument] at intrinsic
          | some expected =>
              have expectedExact : expected = signature :=
                Option.some.inj (by simpa [portSignature?, argument]
                  using intrinsic)
              have bound : index < arguments.length :=
                List.getElem?_eq_some_iff.mp argument |>.1
              have checked :=
                (List.all_eq_true.mp source.property.ref_ports_typed)
                  node (Data.Finite.mem_allFin node)
              rw [nodeData] at checked
              have position := (List.all_eq_true.mp checked)
                index (by simpa using bound)
              rw [owner, argument] at position
              exact (eq_of_beq position).trans expectedExact
      | identity index => simp [portSignature?, nodeData] at intrinsic
  | identity region stored arity =>
      rw [nodeData] at intrinsic
      cases port with
      | head => simp [portSignature?, nodeData] at intrinsic
      | arg index => simp [portSignature?, nodeData] at intrinsic
      | identity index =>
          simp only [portSignature?] at intrinsic
          split at intrinsic
          · rename_i bound
            have storedExact : stored = signature :=
              Option.some.inj (by simpa [portSignature?, bound]
                using intrinsic)
            have checked :=
              (List.all_eq_true.mp source.property.identity_ports_typed)
                node (Data.Finite.mem_allFin node)
            rw [nodeData] at checked
            have position := (List.all_eq_true.mp checked)
              index (by simpa using bound)
            rw [owner] at position
            exact (eq_of_beq position).trans storedExact
          · simp [portSignature?, nodeData, *] at intrinsic

private theorem batchRemovalCandidate_typed_owner
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes)
    (node : (batchRemovalCandidate plan).NodeId)
    (port : CPort) (signature : Sig)
    (intrinsic :
      portSignature? ((batchRemovalCandidate plan).nodes node) port =
        some signature) :
    ∃ wire,
      (batchRemovalCandidate plan).endpointOwner? ⟨node, port⟩ = some wire ∧
      ((batchRemovalCandidate plan).wires wire).sig = signature := by
  have required := portSignature?_some_required
    (batchRemovalCandidate plan) node port signature intrinsic
  obtain ⟨sourceWire, retained, sourceOwner⟩ :=
    batchRemovalCandidate_required_source_owner plan exhausted node port
      required
  let targetWire := retainedWireIndex source removedWires sourceWire retained
  have targetIncident :
      (⟨node, port⟩ : CEndpoint (batchRemovalCandidate plan).nodeCount) ∈
        ((batchRemovalCandidate plan).wires targetWire).endpoints := by
    apply (batchRemovalCandidate_endpoint_iff plan targetWire
      ⟨node, port⟩).mpr
    have sourceIncident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceRetainedNode source removedNodes node, port⟩ sourceWire
      sourceOwner
    have wireExact :
        sourceRetainedWire source removedWires targetWire = sourceWire := by
      unfold targetWire sourceRetainedWire retainedWireIndex
      rw [DenseList.get_index]
    rw [wireExact]
    exact sourceIncident
  have targetOwner := endpointOwner?_eq_of_covered_incident
    (batchRemovalCandidate plan)
    (batchRemovalCandidate_ports_covered_exactly_once plan exhausted)
    node port required targetWire targetIncident
  refine ⟨targetWire, targetOwner, ?_⟩
  rw [batchRemovalCandidate_wire_signature]
  have wireExact :
      sourceRetainedWire source removedWires targetWire = sourceWire := by
    unfold targetWire sourceRetainedWire retainedWireIndex
    rw [DenseList.get_index]
  rw [wireExact]
  apply checked_port_signature source
    (sourceRetainedNode source removedNodes node) port sourceWire sourceOwner
      signature
  rw [← batchRemovalCandidate_portSignature plan node port]
  exact intrinsic

private theorem batchRemovalCandidate_atom_ports_typed
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes) :
    (batchRemovalCandidate plan).AtomPortsTyped := by
  unfold ConcreteDiagram.AtomPortsTyped
  apply List.all_eq_true.mpr
  intro node _
  cases nodeData : (batchRemovalCandidate plan).nodes node with
  | atom region arguments =>
      obtain ⟨headWire, headOwner, headTyped⟩ :=
        batchRemovalCandidate_typed_owner plan exhausted node .head
          (.rel arguments) (by simp [nodeData, portSignature?])
      rw [headOwner, Bool.and_eq_true]
      constructor
      · exact beq_iff_eq.mpr headTyped
      · apply List.all_eq_true.mpr
        intro index member
        have bound : index < arguments.length := List.mem_range.mp member
        obtain ⟨argumentWire, argumentOwner, argumentTyped⟩ :=
          batchRemovalCandidate_typed_owner plan exhausted node (.arg index)
            (arguments[index]'bound)
            (by simp [nodeData, portSignature?,
              List.getElem?_eq_getElem bound])
        rw [argumentOwner, List.getElem?_eq_getElem bound]
        exact beq_iff_eq.mpr argumentTyped
  | ref region definition arguments => simp [nodeData]
  | identity region signature arity => simp [nodeData]

private theorem batchRemovalCandidate_ref_ports_typed
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes) :
    (batchRemovalCandidate plan).RefPortsTyped := by
  unfold ConcreteDiagram.RefPortsTyped
  apply List.all_eq_true.mpr
  intro node _
  cases nodeData : (batchRemovalCandidate plan).nodes node with
  | atom region arguments => simp [nodeData]
  | ref region definition arguments =>
      apply List.all_eq_true.mpr
      intro index member
      have bound : index < arguments.length := List.mem_range.mp member
      obtain ⟨argumentWire, argumentOwner, argumentTyped⟩ :=
        batchRemovalCandidate_typed_owner plan exhausted node (.arg index)
          (arguments[index]'bound)
          (by simp [nodeData, portSignature?,
            List.getElem?_eq_getElem bound])
      rw [argumentOwner, List.getElem?_eq_getElem bound]
      exact beq_iff_eq.mpr argumentTyped
  | identity region signature arity => simp [nodeData]

private theorem batchRemovalCandidate_identity_ports_typed
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes) :
    (batchRemovalCandidate plan).IdentityPortsTyped := by
  unfold ConcreteDiagram.IdentityPortsTyped
  apply List.all_eq_true.mpr
  intro node _
  cases nodeData : (batchRemovalCandidate plan).nodes node with
  | atom region arguments => simp [nodeData]
  | ref region definition arguments => simp [nodeData]
  | identity region signature arity =>
      apply List.all_eq_true.mpr
      intro index member
      have bound : index < arity := List.mem_range.mp member
      obtain ⟨identityWire, identityOwner, identityTyped⟩ :=
        batchRemovalCandidate_typed_owner plan exhausted node
          (.identity index) signature
          (by simp [nodeData, portSignature?, bound])
      rw [identityOwner]
      exact beq_iff_eq.mpr identityTyped

@[simp] theorem batchRemovalCandidate_node_region_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (node : (batchRemovalCandidate plan).NodeId) :
    ((batchRemovalCandidate plan).nodes node).region =
      noRegionRemovalEquiv source
        (source.val.nodes
          (sourceRetainedNode source removedNodes node)).region := by
  rw [show (batchRemovalCandidate plan).nodes node = batchNodeTable plan node by rfl]
  cases nodeData :
      source.val.nodes (sourceRetainedNode source removedNodes node) <;>
    simp [batchNodeTable, nodeData, noRegionRemovalEquiv]
  all_goals apply Fin.ext <;> rfl

private theorem batchRemovalCandidate_wire_scopes_enclose
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires) :
    (batchRemovalCandidate plan).WireScopesEnclose := by
  unfold ConcreteDiagram.WireScopesEnclose
  apply List.all_eq_true.mpr
  rintro ⟨wire, endpoint⟩ occurrence
  have targetIncident := occurrence_incident
    (batchRemovalCandidate plan) wire endpoint occurrence
  have sourceIncident :=
    (batchRemovalCandidate_endpoint_iff plan wire endpoint).mp
      targetIncident
  have sourceOccurrence := incident_occurrence source.val
    (sourceRetainedWire source removedWires wire)
    (sourceRetainedEndpoint source removedNodes endpoint) sourceIncident
  have sourceChecked :=
    (List.all_eq_true.mp source.property.wire_scopes_enclose)
      (sourceRetainedWire source removedWires wire,
        sourceRetainedEndpoint source removedNodes endpoint)
      sourceOccurrence
  apply decide_eq_true
  rw [batchRemovalCandidate_wire_scope_noRegions,
    batchRemovalCandidate_node_region_noRegions,
    batchRemovalCandidate_encloses_noRegions]
  exact of_decide_eq_true sourceChecked

/--
Deleting nodes and wires whose removed wires are exhausted by removed nodes
preserves the entire checked-diagram contract when regions are unchanged.
-/
theorem batchRemovalCandidate_wellFormed_noRegions
    {source : CheckedDiagram definitions}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan : BatchRemovalPlan source [] removedNodes removedWires)
    (exhausted :
      ∀ wire, wire ∈ removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.node ∈ removedNodes) :
    (batchRemovalCandidate plan).WellFormed definitions where
  root_is_sheet := batchRemovalCandidate_rootIsSheet_noRegions plan
  only_root_is_sheet := batchRemovalCandidate_onlyRootIsSheet_noRegions plan
  all_regions_reach_root :=
    batchRemovalCandidate_allRegionsReachRoot_noRegions plan
  references_match := batchRemovalCandidate_referencesMatch plan
  ports_exist := batchRemovalCandidate_ports_exist plan
  no_duplicate_endpoints :=
    batchRemovalCandidate_no_duplicate_endpoints plan exhausted
  ports_covered_exactly_once :=
    batchRemovalCandidate_ports_covered_exactly_once plan exhausted
  atom_ports_typed := batchRemovalCandidate_atom_ports_typed plan exhausted
  ref_ports_typed := batchRemovalCandidate_ref_ports_typed plan exhausted
  identities_have_arity := batchRemovalCandidate_identitiesHaveArity plan
  identity_ports_typed :=
    batchRemovalCandidate_identity_ports_typed plan exhausted
  wire_scopes_enclose := batchRemovalCandidate_wire_scopes_enclose plan

def checkedRegion
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.RegionId :=
  Fin.cast
    (congrArg ConcreteDiagram.regionCount generated).symm region

/-- Equality transport from a checker input to its checked region carrier,
packaged as the canonical finite equivalence. -/
def checkedRegionEquiv
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    Data.Finite.FiniteEquiv candidate.RegionId checked.val.RegionId where
  toFun := checkedRegion generated
  invFun := Fin.cast (congrArg ConcreteDiagram.regionCount generated)
  left_inv := by
    intro region
    apply Fin.ext
    rfl
  right_inv := by
    intro region
    apply Fin.ext
    rfl

/-- Checking transports each region constructor and cut parent exactly along
the canonical carrier equivalence. -/
theorem checkedRegion_data_equiv
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.regions (checkedRegionEquiv generated region) =
      (candidate.regions region).rename (checkedRegionEquiv generated) := by
  cases generated
  cases data : checked.val.regions region <;>
    simp [checkedRegionEquiv, checkedRegion, CRegion.rename, data]

end Internal

theorem checkedRegion_injective
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    {left right : candidate.RegionId}
    (same :
      Internal.checkedRegion generated left = Internal.checkedRegion generated right) :
    left = right := by
  unfold Internal.checkedRegion at same
  apply Fin.ext
  simpa using congrArg Fin.val same

namespace Internal

theorem checkedRegion_encloses
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (outer inner : candidate.RegionId) :
    checked.val.Encloses
        (checkedRegion generated outer) (checkedRegion generated inner) ↔
      candidate.Encloses outer inner := by
  cases generated
  rfl

def checkedNode
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (node : candidate.NodeId) :
    checked.val.NodeId :=
  Fin.cast
    (congrArg ConcreteDiagram.nodeCount generated).symm node

def checkedWire
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    checked.val.WireId :=
  Fin.cast
    (congrArg ConcreteDiagram.wireCount generated).symm wire

theorem checkedWire_signature_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).sig =
      (candidate.wires wire).sig := by
  subst candidate
  rfl

def checkedEndpoint
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (endpoint : CEndpoint candidate.nodeCount) :
    CEndpoint checked.val.nodeCount :=
  { node := checkedNode generated endpoint.node
    port := endpoint.port }

theorem checkedWire_scope_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).scope =
      checkedRegion generated (candidate.wires wire).scope := by
  subst candidate
  rfl

/-- Ordered local-wire enumeration is preserved when a well-formed checker
reindexes its accepted candidate. -/
theorem checkedWiresAt_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.wiresAt (checkedRegion generated region) =
      (candidate.wiresAt region).map (checkedWire generated) := by
  cases generated
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  have regionExact : checkedRegion rfl region = region := by
    apply Fin.ext
    rfl
  rw [regionExact]
  let wires :=
    (Data.Finite.allFin checked.val.wireCount).filter fun wire =>
      (checked.val.wires wire).scope == region
  change wires = wires.map (checkedWire rfl)
  calc
    wires = wires.map id := (List.map_id wires).symm
    _ = wires.map (checkedWire rfl) := by
      apply List.map_congr_left
      intro wire _member
      apply Fin.ext
      rfl

/-- Ordered local-node enumeration is preserved when a well-formed checker
reindexes its accepted candidate. -/
theorem checkedNodesAt_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.nodesAt (checkedRegion generated region) =
      (candidate.nodesAt region).map (checkedNode generated) := by
  cases generated
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  have regionExact : checkedRegion rfl region = region := by
    apply Fin.ext
    rfl
  rw [regionExact]
  let nodes :=
    (Data.Finite.allFin checked.val.nodeCount).filter fun node =>
      (checked.val.nodes node).region == region
  change nodes = nodes.map (checkedNode rfl)
  calc
    nodes = nodes.map id := (List.map_id nodes).symm
    _ = nodes.map (checkedNode rfl) := by
      apply List.map_congr_left
      intro node _member
      apply Fin.ext
      rfl

theorem checkedWire_endpoints_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).endpoints =
      (candidate.wires wire).endpoints.map
        (checkedEndpoint generated) := by
  cases generated
  unfold checkedWire checkedEndpoint checkedNode
  simp

/-- Endpoint ownership is transported exactly when a checked well-formed
candidate is reindexed. -/
theorem checkedEndpoint_owner_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (endpoint : CEndpoint candidate.nodeCount) :
    checked.val.endpointOwner? (checkedEndpoint generated endpoint) =
      (candidate.endpointOwner? endpoint).map
        (checkedWire generated) := by
  subst candidate
  have endpointExact : checkedEndpoint rfl endpoint = endpoint := by
    cases endpoint
    congr
  rw [endpointExact]
  cases owner : checked.val.endpointOwner? endpoint with
  | none => rfl
  | some wire =>
      simp only [Option.map_some, Option.some.injEq]
      apply Fin.ext
      rfl

def checkedNodeData
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    CNode candidate.regionCount definitions.length →
      CNode checked.val.regionCount definitions.length
  | .atom region args =>
      .atom (checkedRegion generated region) args
  | .ref region definition args =>
      .ref (checkedRegion generated region) definition args
  | .identity region sig arity =>
      .identity (checkedRegion generated region) sig arity

theorem checkedNodeData_relocate
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (node : CNode sourceRegionCount definitions.length)
    (region : candidate.RegionId) :
    checkedNodeData generated (node.relocate region) =
      node.relocate (checkedRegion generated region) := by
  cases node <;> rfl

private def checkedRegionData
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    CRegion candidate.regionCount → CRegion checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (checkedRegion generated parent)

theorem checkedRoot_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    checked.val.root = checkedRegion generated candidate.root := by
  cases generated
  rfl

theorem checkedRegion_data_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.regions (checkedRegion generated region) =
      checkedRegionData generated (candidate.regions region) := by
  cases generated
  cases data : checked.val.regions region <;>
    simp [checkedRegion, checkedRegionData, data]

theorem checkedRegion_data_transport_sheet
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId)
    (data : candidate.regions region = .sheet) :
    checked.val.regions (checkedRegion generated region) = .sheet := by
  rw [checkedRegion_data_transport]
  simp [checkedRegionData, data]

theorem checkedRegion_data_transport_cut
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region parent : candidate.RegionId)
    (data : candidate.regions region = .cut parent) :
    checked.val.regions (checkedRegion generated region) =
      .cut (checkedRegion generated parent) := by
  rw [checkedRegion_data_transport]
  simp [checkedRegionData, data]

theorem checkedNode_data_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (node : candidate.NodeId) :
    checked.val.nodes (checkedNode generated node) =
      checkedNodeData generated (candidate.nodes node) := by
  cases generated
  cases data : checked.val.nodes node <;>
    simp [checkedNode, checkedNodeData, checkedRegion, data]

/-- Checking followed by no-region dense renaming is exactly candidate
renaming through the corresponding composite equivalence. -/
theorem checkedRegion_data_rename_noRegions
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (regions : Data.Finite.FiniteEquiv candidate.RegionId
      (Fin (retainedRegions checked []).length))
    (exact : ∀ region,
      regions region =
        noRegionRemovalEquiv checked (checkedRegion generated region))
    (region : candidate.RegionId) :
    (checked.val.regions (checkedRegion generated region)).rename
        (noRegionRemovalEquiv checked) =
      (candidate.regions region).rename regions := by
  rw [checkedRegion_data_transport]
  cases data : candidate.regions region <;>
    simp [checkedRegionData, data, CRegion.rename, exact]

theorem checkedNode_data_rename_noRegions
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (regions : Data.Finite.FiniteEquiv candidate.RegionId
      (Fin (retainedRegions checked []).length))
    (exact : ∀ region,
      regions region =
        noRegionRemovalEquiv checked (checkedRegion generated region))
    (node : candidate.NodeId) :
    (checked.val.nodes (checkedNode generated node)).rename
        (noRegionRemovalEquiv checked) =
      (candidate.nodes node).rename regions := by
  rw [checkedNode_data_transport]
  cases data : candidate.nodes node <;>
    simp [checkedNodeData, data, CNode.rename, exact]

end Internal

end ConcreteWireQuantifier

end VisualProof
