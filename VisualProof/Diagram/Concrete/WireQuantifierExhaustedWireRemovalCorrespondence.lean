import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemoval
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalitySupport

namespace VisualProof

universe u v w

namespace ConcreteWireQuantifier

namespace ExhaustedWireRemovalSemantics

namespace Internal

abbrev Target
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :=
  ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate source removed

end Internal

open Internal

private def retainedRegions
    (source : CheckedDiagram definitions) :
    List source.val.RegionId :=
  source.val.regionsList.filter fun region =>
    decide (region ∉ ([] : List source.val.RegionId))

/-- The count-preserving region image into singleton-wire deletion. -/
def targetRegion
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    (Target source removed).RegionId :=
  DenseList.index (retainedRegions source) region (by
    simp [retainedRegions, ConcreteDiagram.regionsList,
      Data.Finite.mem_allFin])

/-- Singleton-wire deletion retains regions in their exact dense order. -/
@[simp] theorem targetRegion_val
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    (targetRegion source removed region).val = region.val := by
  have keepAll :
      ∀ values : List (Fin source.val.regionCount),
        values.filter (fun _ => true) = values := by
    intro values
    induction values <;> simp_all
  have selected := congrArg Fin.val
    (DenseList.get_index (retainedRegions source) region (by
      simp [retainedRegions, ConcreteDiagram.regionsList,
        Data.Finite.mem_allFin]))
  simpa [targetRegion, retainedRegions, ConcreteDiagram.regionsList,
    Data.Finite.allFin_eq_finRange, keepAll] using selected

@[simp] theorem target_regionCount
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    (Target source removed).regionCount = source.val.regionCount := by
  have keepAll :
      ∀ values : List (Fin source.val.regionCount),
        values.filter (fun _ => true) = values := by
    intro values
    induction values <;> simp_all
  simp [Target,
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate,
    ConcreteDiagram.regionsList,
    Data.Finite.allFin_eq_finRange, keepAll]

theorem targetRegion_injective
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    Function.Injective (targetRegion source removed) := by
  intro left right same
  calc
    left = (retainedRegions source).get
        (targetRegion source removed left) :=
      (DenseList.get_index (retainedRegions source) left _).symm
    _ = (retainedRegions source).get
        (targetRegion source removed right) := congrArg _ same
    _ = right :=
      DenseList.get_index (retainedRegions source) right _

/-- Pull one dense target region back to its source region. -/
def sourceRegion
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : (Target source removed).RegionId) :
    source.val.RegionId :=
  (retainedRegions source).get region

@[simp] theorem targetRegion_sourceRegion
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : (Target source removed).RegionId) :
    targetRegion source removed (sourceRegion source removed region) =
      region := by
  unfold targetRegion sourceRegion
  exact DenseList.index_get (retainedRegions source)
    ((Data.Finite.allFin_nodup source.val.regionCount).filter _) region

@[simp] theorem sourceRegion_targetRegion
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    sourceRegion source removed (targetRegion source removed region) =
      region := by
  exact DenseList.get_index (retainedRegions source) region _

/-- Exact forward copied region shape. -/
theorem targetRegion_shape
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    (Target source removed).regions (targetRegion source removed region) =
      match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (targetRegion source removed parent) := by
  unfold Target targetRegion retainedRegions
  simp only [
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate,
    DenseList.get_index]
  unfold DenseList.index
  split <;> simp_all <;> apply Fin.ext <;> rfl

@[simp] theorem target_root
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    (Target source removed).root =
      targetRegion source removed source.val.root := by
  unfold Target targetRegion retainedRegions
  simp only [
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate]
  rfl

/-- Exact inverse copied region shape. -/
theorem sourceRegion_shape
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : (Target source removed).RegionId) :
    source.val.regions (sourceRegion source removed region) =
      match (Target source removed).regions region with
      | .sheet => .sheet
      | .cut parent => .cut (sourceRegion source removed parent) := by
  have copied :=
    targetRegion_shape source removed (sourceRegion source removed region)
  rw [targetRegion_sourceRegion] at copied
  rw [copied]
  cases source.val.regions (sourceRegion source removed region) <;> simp

theorem targetRegion_climb
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    ∀ (steps : Nat) (region : source.val.RegionId),
      (Target source removed).climb steps
          (targetRegion source removed region) =
        (source.val.climb steps region).map
          (targetRegion source removed) := by
  intro steps
  induction steps with
  | zero => intro region; rfl
  | succ steps induction =>
      intro region
      cases regionData : source.val.regions region with
      | sheet =>
          simp [ConcreteDiagram.climb,
            targetRegion_shape, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, targetRegion_shape,
            regionData] using induction parent

theorem targetRegion_encloses_iff
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (outer inner : source.val.RegionId) :
    (Target source removed).Encloses
        (targetRegion source removed outer)
        (targetRegion source removed inner) ↔
      source.val.Encloses outer inner := by
  rw [ConcreteElaboration.encloses_iff_exists,
    ConcreteElaboration.encloses_iff_exists]
  constructor
  · rintro ⟨steps, climbed⟩
    let sourceSteps : Fin (source.val.regionCount + 1) :=
      ⟨steps.val, by simpa using steps.isLt⟩
    have mapped :=
      targetRegion_climb source removed steps.val inner
    rw [mapped] at climbed
    change
      (source.val.climb sourceSteps inner).map
          (targetRegion source removed) =
        some (targetRegion source removed outer) at climbed
    cases sourceClimb : source.val.climb sourceSteps inner with
    | none => simp [sourceClimb] at climbed
    | some reached =>
        rw [sourceClimb] at climbed
        have same :=
          targetRegion_injective source removed
            (Option.some.inj climbed)
        exact ⟨sourceSteps, by
          simpa [sourceSteps] using
            sourceClimb.trans (congrArg some same)⟩
  · rintro ⟨steps, climbed⟩
    let targetSteps : Fin ((Target source removed).regionCount + 1) :=
      ⟨steps.val, by
        simpa only [target_regionCount] using steps.isLt⟩
    exact ⟨targetSteps, by
      simpa [targetSteps] using
        (targetRegion_climb source removed steps.val inner).trans
          (by rw [climbed]; rfl)⟩

theorem target_find_enclosing
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (site : source.val.RegionId) :
    ∀ regions : List source.val.RegionId,
      ((regions.map (targetRegion source removed)).find? fun candidate =>
        decide ((Target source removed).Encloses candidate
          (targetRegion source removed site))) =
      (regions.find? fun candidate =>
        decide (source.val.Encloses candidate site)).map
          (targetRegion source removed) := by
  intro regions
  induction regions with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.find?_cons]
      have samePredicate :
          (Target source removed).Encloses
              (targetRegion source removed head)
              (targetRegion source removed site) ↔
            source.val.Encloses head site :=
        targetRegion_encloses_iff source removed head site
      by_cases encloses : source.val.Encloses head site
      · have targetEncloses := samePredicate.mpr encloses
        simp [encloses, targetEncloses]
      · have targetRejects :=
          fun accepted => encloses (samePredicate.mp accepted)
        have rejected :
            decide ((Target source removed).Encloses
              (targetRegion source removed head)
              (targetRegion source removed site)) = false := by
          exact decide_eq_false targetRejects
        rw [rejected]
        simp [encloses, induction]

def Internal.retainedNodes
    (source : CheckedDiagram definitions) :
    List source.val.NodeId :=
  source.val.nodesList.filter fun node =>
    decide (node ∉ ([] : List source.val.NodeId))

/-- The count-preserving node image into singleton-wire deletion. -/
def targetNode
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : source.val.NodeId) :
    (Target source removed).NodeId :=
  DenseList.index (retainedNodes source) node (by
    simp [retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.mem_allFin])

/-- Pull one dense target node back to its source node. -/
def sourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : (Target source removed).NodeId) :
    source.val.NodeId :=
  (retainedNodes source).get node

@[simp] theorem targetNode_sourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : (Target source removed).NodeId) :
    targetNode source removed (sourceNode source removed node) =
      node := by
  unfold targetNode sourceNode
  exact DenseList.index_get (retainedNodes source)
    ((Data.Finite.allFin_nodup source.val.nodeCount).filter _) node

@[simp] theorem sourceNode_targetNode
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : source.val.NodeId) :
    sourceNode source removed (targetNode source removed node) =
      node :=
  DenseList.get_index (retainedNodes source) node _

/-- Exact forward copied node shape. -/
theorem targetNode_shape
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : source.val.NodeId) :
    (Target source removed).nodes (targetNode source removed node) =
      match source.val.nodes node with
      | .atom region args =>
          .atom (targetRegion source removed region) args
      | .ref region definition args =>
          .ref (targetRegion source removed region) definition args
      | .identity region sig arity =>
          .identity (targetRegion source removed region) sig arity := by
  unfold Target targetNode targetRegion retainedNodes retainedRegions
  simp only [
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate]
  simp only [DenseList.get_index]
  unfold DenseList.index
  split <;> simp_all <;> apply Fin.ext <;> rfl

/-- Exact copied node shape, including the dense region image. -/
theorem sourceNode_shape
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : (Target source removed).NodeId) :
    source.val.nodes (sourceNode source removed node) =
      match (Target source removed).nodes node with
      | .atom region args =>
          .atom (sourceRegion source removed region) args
      | .ref region definition args =>
          .ref (sourceRegion source removed region) definition args
      | .identity region sig arity =>
          .identity (sourceRegion source removed region) sig arity := by
  have copied :=
    targetNode_shape source removed (sourceNode source removed node)
  rw [targetNode_sourceNode] at copied
  rw [copied]
  cases source.val.nodes (sourceNode source removed node) <;> simp

@[simp] theorem sourceNode_region
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : (Target source removed).NodeId) :
    sourceRegion source removed ((Target source removed).nodes node).region =
      (source.val.nodes (sourceNode source removed node)).region := by
  have shape := congrArg CNode.region
    (sourceNode_shape source removed node)
  split at shape <;> simp_all <;> rfl

/-- The dense target index of one retained source wire. -/
def targetWire
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : source.val.WireId)
    (survives : wire ≠ removed) :
    (Target source removed).WireId :=
  DenseList.index
    (ConcreteDiagram.IdentityNormalizationCore.retainedWires
      source.val [removed])
    wire (by
      simpa [ConcreteDiagram.IdentityNormalizationCore.retainedWires,
        ConcreteDiagram.wiresList, Data.Finite.mem_allFin] using survives)

/-- Pull one dense target wire back to its retained source wire. -/
def sourceWire
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : (Target source removed).WireId) :
    source.val.WireId :=
  (ConcreteDiagram.IdentityNormalizationCore.retainedWires
    source.val [removed]).get wire

theorem sourceWire_ne
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : (Target source removed).WireId) :
    sourceWire source removed wire ≠ removed := by
  have member :=
    List.get_mem
      (ConcreteDiagram.IdentityNormalizationCore.retainedWires
        source.val [removed]) wire
  simpa [sourceWire,
    ConcreteDiagram.IdentityNormalizationCore.retainedWires] using
    (List.mem_filter.mp member).2

@[simp] theorem sourceWire_targetWire
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : source.val.WireId)
    (survives : wire ≠ removed) :
    sourceWire source removed (targetWire source removed wire survives) =
      wire :=
  DenseList.get_index
    (ConcreteDiagram.IdentityNormalizationCore.retainedWires
      source.val [removed])
    wire _

@[simp] theorem targetWire_sourceWire
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : (Target source removed).WireId) :
    targetWire source removed (sourceWire source removed wire)
        (sourceWire_ne source removed wire) =
      wire := by
  apply Fin.ext
  change
    (DenseList.index
      (ConcreteDiagram.IdentityNormalizationCore.retainedWires
        source.val [removed])
      ((ConcreteDiagram.IdentityNormalizationCore.retainedWires
        source.val [removed]).get wire) _).val =
      wire.val
  rw [DenseList.index_get
    (ConcreteDiagram.IdentityNormalizationCore.retainedWires
      source.val [removed])
    ((Data.Finite.allFin_nodup source.val.wireCount).filter _) wire]

@[simp] theorem targetWire_signature
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : source.val.WireId)
    (survives : wire ≠ removed) :
    ((Target source removed).wires
        (targetWire source removed wire survives)).sig =
      (source.val.wires wire).sig := by
  unfold targetWire Target
  simp only [
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate]
  rw [DenseList.get_index]

@[simp] theorem targetWire_scope
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : source.val.WireId)
    (survives : wire ≠ removed) :
    ((Target source removed).wires
        (targetWire source removed wire survives)).scope =
      targetRegion source removed (source.val.wires wire).scope := by
  let target := targetWire source removed wire survives
  have sourceExact :
      (ConcreteDiagram.IdentityNormalizationCore.retainedWires
          source.val [removed]).get target =
        wire := by
    exact DenseList.get_index
      (ConcreteDiagram.IdentityNormalizationCore.retainedWires
        source.val [removed]) wire _
  change
    targetRegion source removed
        (source.val.wires
          ((ConcreteDiagram.IdentityNormalizationCore.retainedWires
            source.val [removed]).get target)).scope =
      targetRegion source removed (source.val.wires wire).scope
  exact congrArg (targetRegion source removed)
    (congrArg (fun candidate => (source.val.wires candidate).scope)
      sourceExact)

@[simp] theorem sourceWire_scope
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : (Target source removed).WireId) :
    sourceRegion source removed
        ((Target source removed).wires wire).scope =
      (source.val.wires (sourceWire source removed wire)).scope := by
  apply targetRegion_injective source removed
  rw [targetRegion_sourceRegion]
  calc
    ((Target source removed).wires wire).scope =
        ((Target source removed).wires
          (targetWire source removed
            (sourceWire source removed wire)
            (sourceWire_ne source removed wire))).scope :=
      congrArg (fun candidate =>
        ((Target source removed).wires candidate).scope)
        (targetWire_sourceWire source removed wire).symm
    _ = targetRegion source removed
          (source.val.wires (sourceWire source removed wire)).scope :=
      targetWire_scope source removed
        (sourceWire source removed wire)
        (sourceWire_ne source removed wire)

@[simp] theorem sourceWire_signature
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : (Target source removed).WireId) :
    (source.val.wires (sourceWire source removed wire)).sig =
      ((Target source removed).wires wire).sig := by
  rw [← targetWire_signature source removed
    (sourceWire source removed wire) (sourceWire_ne source removed wire)]
  simp

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

private theorem childrenOf_map_exact
    (target : ConcreteDiagram definitionCount)
    (source : ConcreteDiagram definitionCount)
    (targetRegionId : target.RegionId)
    (sourceRegionId : source.RegionId)
    (regionMap : target.RegionId → source.RegionId)
    (regionsExact :
      target.regionsList.map regionMap = source.regionsList)
    (parentExact :
      ∀ child,
        (match target.regions child with
          | .sheet => false
          | .cut parent => parent == targetRegionId) =
        (match source.regions (regionMap child) with
          | .sheet => false
          | .cut parent => parent == sourceRegionId)) :
    (target.childrenOf targetRegionId).map regionMap =
      source.childrenOf sourceRegionId := by
  unfold ConcreteDiagram.childrenOf
  have filters :
      target.regionsList.filter
          (fun child =>
            match target.regions child with
            | .sheet => false
            | .cut parent => parent == targetRegionId) =
        target.regionsList.filter
          ((fun child =>
            match source.regions child with
            | .sheet => false
            | .cut parent => parent == sourceRegionId) ∘ regionMap) := by
    apply List.filter_congr
    intro child _
    exact parentExact child
  calc
    _ =
        (target.regionsList.filter
          ((fun child =>
            match source.regions child with
            | .sheet => false
            | .cut parent => parent == sourceRegionId) ∘
              regionMap)).map regionMap :=
      congrArg (List.map regionMap) filters
    _ =
        (target.regionsList.map regionMap).filter
          (fun child =>
            match source.regions child with
            | .sheet => false
            | .cut parent => parent == sourceRegionId) := by
      rw [List.filter_map]
    _ = _ :=
      congrArg
        (List.filter fun child =>
          match source.regions child with
          | .sheet => false
          | .cut parent => parent == sourceRegionId)
        regionsExact

/-- Exact stored child order induced by singleton-wire deletion. -/
theorem childrenOf_sources
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    ((Target source removed).childrenOf
        (targetRegion source removed region)).map
          (sourceRegion source removed) =
      source.val.childrenOf region := by
  have allSources :
      (Target source removed).regionsList.map
          (sourceRegion source removed) =
        source.val.regionsList := by
    calc
      _ = retainedRegions source := by
        simpa [ConcreteDiagram.regionsList, sourceRegion] using
          map_get_allFin (retainedRegions source)
      _ = source.val.regionsList := by
        simp [retainedRegions, ConcreteDiagram.regionsList]
  apply childrenOf_map_exact
    (Target source removed) source.val
    (targetRegion source removed region) region
    (sourceRegion source removed) allSources
  intro child
  have copied := sourceRegion_shape source removed child
  cases targetData : (Target source removed).regions child with
  | sheet =>
      rw [targetData] at copied
      simp [copied]
  | cut parent =>
      rw [targetData] at copied
      simp only [copied]
      apply decide_eq_decide.mpr
      constructor
      · intro same
        calc
          sourceRegion source removed parent =
              sourceRegion source removed
                (targetRegion source removed region) :=
            congrArg (sourceRegion source removed) same
          _ = region := sourceRegion_targetRegion source removed region
      · intro same
        calc
          parent =
              targetRegion source removed
                (sourceRegion source removed parent) :=
            (targetRegion_sourceRegion source removed parent).symm
          _ = targetRegion source removed region :=
            congrArg (targetRegion source removed) same

/-- Exact forward child order induced by singleton-wire deletion. -/
theorem target_childrenOf
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    (Target source removed).childrenOf
        (targetRegion source removed region) =
      (source.val.childrenOf region).map
        (targetRegion source removed) := by
  calc
    _ = (((Target source removed).childrenOf
          (targetRegion source removed region)).map
            (sourceRegion source removed)).map
          (targetRegion source removed) := by
      symm
      rw [List.map_map]
      simp [Function.comp_def]
    _ = _ := congrArg (List.map (targetRegion source removed))
      (childrenOf_sources source removed region)

/-- Exact stored node order induced by singleton-wire deletion. -/
theorem nodesAt_sources
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    ((Target source removed).nodesAt
        (targetRegion source removed region)).map
          (sourceNode source removed) =
      source.val.nodesAt region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  have targetFilter :
      (Data.Finite.allFin (Target source removed).nodeCount).filter
          (fun node =>
            ((Target source removed).nodes node).region ==
              targetRegion source removed region) =
        (Data.Finite.allFin (Target source removed).nodeCount).filter
          ((fun candidate =>
            (source.val.nodes candidate).region == region) ∘
              sourceNode source removed) := by
    apply List.filter_congr
    intro node _
    apply decide_eq_decide.mpr
    have nodeRegion :
        ((Target source removed).nodes node).region =
          targetRegion source removed
            (source.val.nodes (sourceNode source removed node)).region := by
      have mapped := congrArg (targetRegion source removed)
        (sourceNode_region source removed node)
      simpa only [targetRegion_sourceRegion] using mapped
    constructor
    · intro same
      apply targetRegion_injective source removed
      simpa [nodeRegion] using same
    · intro same
      rw [nodeRegion, same]
  rw [targetFilter, ← List.filter_map]
  have allSources :
      (Data.Finite.allFin (Target source removed).nodeCount).map
          (sourceNode source removed) =
        retainedNodes source := by
    simpa [sourceNode] using map_get_allFin (retainedNodes source)
  rw [allSources]
  simp [retainedNodes, ConcreteDiagram.nodesList]

/--
The source origins of the dense target wires at a retained region are exactly
the source local-wire order with the removed wire filtered out.
-/
theorem wiresAt_sources
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    ((Target source removed).wiresAt
        (targetRegion source removed region)).map
          (sourceWire source removed) =
      (source.val.wiresAt region).filter
        (fun wire => decide (wire ≠ removed)) := by
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  have targetFilter :
      (Data.Finite.allFin (Target source removed).wireCount).filter
          (fun wire =>
            ((Target source removed).wires wire).scope ==
              targetRegion source removed region) =
        (Data.Finite.allFin (Target source removed).wireCount).filter
          ((fun candidate =>
            (source.val.wires candidate).scope == region) ∘
              sourceWire source removed) := by
    apply List.filter_congr
    intro wire _
    apply decide_eq_decide.mpr
    constructor
    · intro same
      apply targetRegion_injective source removed
      rw [← same]
      exact
        (targetWire_scope source removed
          (sourceWire source removed wire)
          (sourceWire_ne source removed wire)).symm.trans
          (congrArg
            (fun candidate =>
              ((Target source removed).wires candidate).scope)
            (targetWire_sourceWire source removed wire))
    · intro same
      rw [← targetWire_sourceWire source removed wire,
        targetWire_scope, same]
  rw [targetFilter, ← List.filter_map]
  have allSources :
      (Data.Finite.allFin (Target source removed).wireCount).map
          (sourceWire source removed) =
        ConcreteDiagram.IdentityNormalizationCore.retainedWires
          source.val [removed] := by
    simpa [sourceWire] using
      map_get_allFin
        (ConcreteDiagram.IdentityNormalizationCore.retainedWires
          source.val [removed])
  rw [allSources]
  simp only [
    ConcreteDiagram.IdentityNormalizationCore.retainedWires,
    List.filter_filter]
  apply List.filter_congr
  intro candidate _
  simpa using
    (Bool.and_comm
      ((source.val.wires candidate).scope == region)
      (decide (candidate ≠ removed)))

/-- Exact local signature order induced by singleton-wire deletion. -/
theorem wiresAt_signatures
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId) :
    ((Target source removed).wiresAt
        (targetRegion source removed region)).map
          (fun wire => ((Target source removed).wires wire).sig) =
      ((source.val.wiresAt region).filter
        (fun wire => decide (wire ≠ removed))).map
          (fun wire => (source.val.wires wire).sig) := by
  rw [← wiresAt_sources source removed region, List.map_map]
  apply List.map_congr_left
  intro wire _
  exact sourceWire_signature source removed wire

/--
A target compiler context names exactly the surviving members of its source
context, in source order.
-/
def ContextsCorrespond
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext : ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val) : Prop :=
  targetContext.ids.map (sourceWire source removed) =
    sourceContext.ids.filter (fun wire => decide (wire ≠ removed))

/--
Corresponding contexts above the deleted wire have the same ordered
signature vector.  The equality is structural: singleton deletion preserves
the order and signature of every surviving wire.
-/
theorem corresponding_sigs_eq
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids) :
    targetContext.sigs = sourceContext.sigs := by
  unfold ConcreteElaboration.WireContext.sigs
  calc
    targetContext.ids.map
          (fun wire => ((Target source removed).wires wire).sig) =
        (targetContext.ids.map (sourceWire source removed)).map
          (fun wire => (source.val.wires wire).sig) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro wire _
      exact sourceWire_signature source removed wire
    _ =
        (sourceContext.ids.filter
          (fun wire => decide (wire ≠ removed))).map
            (fun wire => (source.val.wires wire).sig) := by
      rw [correspond]
    _ = sourceContext.ids.map
          (fun wire => (source.val.wires wire).sig) := by
      rw [List.filter_eq_self.mpr]
      intro wire member
      simpa using (fun (same : wire = removed) =>
        removedAbsent (same ▸ member))

private def consEq
    (head : leftHead = rightHead)
    (tail : leftTail = rightTail) :
    leftHead :: leftTail = rightHead :: rightTail := by
  cases head
  cases tail
  rfl

private theorem consEq_cast_here
    (head : leftHead = rightHead)
    (tail : leftTail = rightTail) :
    consEq head tail ▸
        (Var.here : Var (leftHead :: leftTail) leftHead) =
      (head ▸ (Var.here :
        Var (rightHead :: rightTail) rightHead)) := by
  cases head
  cases tail
  rfl

private theorem consEq_cast_there
    (head : leftHead = rightHead)
    (tail : leftTail = rightTail)
    (value : Var leftTail sig) :
    consEq head tail ▸ (Var.there value :
        Var (leftHead :: leftTail) sig) =
      (Var.there (tail ▸ value) :
        Var (rightHead :: rightTail) sig) := by
  cases head
  cases tail
  rfl

private def sourceWire_sigs_eq
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    (ids : List (Target source removed).WireId) →
      ids.map (fun wire => ((Target source removed).wires wire).sig) =
        (ids.map (sourceWire source removed)).map
          (fun wire => (source.val.wires wire).sig)
  | [] => rfl
  | head :: tail =>
      consEq
        (sourceWire_signature source removed head).symm
        (sourceWire_sigs_eq source removed tail)

private theorem origin_cast_sourceWire_sigs
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (ids : List (Target source removed).WireId)
    {sig : Sig}
    (value :
      Var
        (ids.map
          (fun wire => ((Target source removed).wires wire).sig)) sig) :
    ConcreteElaboration.WireContext.origin source.val
        (ids.map (sourceWire source removed))
        (sourceWire_sigs_eq source removed ids ▸ value) =
      sourceWire source removed
        (ConcreteElaboration.WireContext.origin
          (Target source removed) ids value) := by
  induction ids with
  | nil => exact nomatch value
  | cons head tail induction =>
      unfold sourceWire_sigs_eq
      cases value with
      | here =>
          simp [consEq_cast_here,
            ConcreteElaboration.WireContext.origin]
          change sourceWire source removed head =
            sourceWire source removed head
          rfl
      | there value =>
          simpa [consEq_cast_there,
            ConcreteElaboration.WireContext.origin] using induction value

private theorem cast_corresponding_origin
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    {sig : Sig}
    (value : Var targetContext.sigs sig) :
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        (corresponding_sigs_eq source removed targetContext sourceContext
          correspond removedAbsent ▸ value) =
      sourceWire source removed
        (ConcreteElaboration.WireContext.origin
          (Target source removed) targetContext.ids value) := by
  have idsExact :
      targetContext.ids.map (sourceWire source removed) =
        sourceContext.ids := by
    calc
      _ =
          sourceContext.ids.filter
            (fun wire => decide (wire ≠ removed)) := correspond
      _ = sourceContext.ids := by
        rw [List.filter_eq_self.mpr]
        intro wire member
        simpa using (fun (same : wire = removed) =>
          removedAbsent (same ▸ member))
  cases targetContext with
  | mk targetIds =>
      cases sourceContext with
      | mk sourceIds =>
          dsimp only [ConcreteElaboration.WireContext.ids] at idsExact
          subst sourceIds
          have proofExact :
              corresponding_sigs_eq source removed
                  ⟨targetIds⟩
                  ⟨targetIds.map (sourceWire source removed)⟩
                  correspond removedAbsent =
                sourceWire_sigs_eq source removed targetIds :=
            Subsingleton.elim _ _
          rw [proofExact]
          exact origin_cast_sourceWire_sigs source removed targetIds value

theorem empty_contexts_correspond
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    ContextsCorrespond source removed
      (ConcreteElaboration.WireContext.empty (Target source removed))
      (ConcreteElaboration.WireContext.empty source.val) := by
  rfl

theorem extend_contexts_correspond
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    {targetContext :
      ConcreteElaboration.WireContext (Target source removed)}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId) :
    ContextsCorrespond source removed
      (targetContext.extend (targetRegion source removed region))
      (sourceContext.extend region) := by
  unfold ContextsCorrespond ConcreteElaboration.WireContext.extend at *
  simp only [List.map_append, List.filter_append, wiresAt_sources,
    correspond]

private theorem source_visible
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    {targetContext :
      ConcreteElaboration.WireContext (Target source removed)}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (wire : (Target source removed).WireId)
    (member : wire ∈ targetContext.ids) :
    sourceWire source removed wire ∈ sourceContext.ids := by
  have mapped :
      sourceWire source removed wire ∈
        targetContext.ids.map (sourceWire source removed) :=
    List.mem_map.mpr ⟨wire, member, rfl⟩
  rw [correspond] at mapped
  exact (List.mem_filter.mp mapped).1

theorem Internal.target_visible
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    {targetContext :
      ConcreteElaboration.WireContext (Target source removed)}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (wire : source.val.WireId)
    (survives : wire ≠ removed)
    (member : wire ∈ sourceContext.ids) :
    targetWire source removed wire survives ∈ targetContext.ids := by
  have filtered :
      wire ∈ sourceContext.ids.filter
        (fun candidate => decide (candidate ≠ removed)) :=
    List.mem_filter.mpr ⟨member, by simpa using survives⟩
  rw [← correspond] at filtered
  obtain ⟨candidate, candidateMember, candidateExact⟩ :=
    List.mem_map.mp filtered
  have sameTarget :
      candidate = targetWire source removed wire survives := by
    calc
      candidate =
          targetWire source removed
            (sourceWire source removed candidate)
            (sourceWire_ne source removed candidate) :=
        (targetWire_sourceWire source removed candidate).symm
      _ = targetWire source removed wire survives := by
        subst wire
        rfl
  simpa [sameTarget] using candidateMember

/-- The exact typed inclusion of a surviving target context into its source. -/
def contextEmbedding
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext) :
    WireRenaming targetContext.sigs sourceContext.sigs :=
  InsertionCompilation.NaturalityInternal.contextEmbedding
    (Target source removed) source.val targetContext.ids sourceContext.ids
    (sourceWire source removed)
    (sourceWire_signature source removed)
    (source_visible source removed correspond)

theorem contextEmbedding_action
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        (contextEmbedding source removed targetContext sourceContext
          correspond value) =
      sourceWire source removed
        (ConcreteElaboration.WireContext.origin
          (Target source removed) targetContext.ids value) :=
  InsertionCompilation.NaturalityInternal.contextEmbedding_origin
    (Target source removed) source.val targetContext.ids sourceContext.ids
    (sourceWire source removed)
    (sourceWire_signature source removed)
    (source_visible source removed correspond) value

/--
The inverse variable map on a context that does not contain the deleted wire.
Strictly-above contexts satisfy this premise; the dying scope's local context
deliberately does not.
-/
def contextProjection
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids) :
    WireRenaming sourceContext.sigs targetContext.sigs :=
  fun {_} value =>
    let wire :=
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        value
    let member :=
      InsertionCompilation.NaturalityInternal.origin_member source.val
        sourceContext.ids value
    let survives : wire ≠ removed :=
      fun same => removedAbsent (same ▸ member)
    let targetMember :=
      target_visible source removed correspond wire survives member
    InsertionCompilation.NaturalityInternal.castVar
      ((targetWire_signature source removed wire survives).trans
        (ConcreteElaboration.WireContext.origin_signature source.val
          sourceContext.ids value))
      (InsertionCompilation.NaturalityInternal.varForMember
        (Target source removed)
        targetContext.ids (targetWire source removed wire survives)
        targetMember)

/--
Project one source variable known individually to survive deletion.  Unlike
`contextProjection`, this does not require the whole source context to omit
the removed wire; it is the local inverse used below the dying binder.
-/
def survivingProjection
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    {sig : Sig}
    (value : Var sourceContext.sigs sig)
    (survives :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        removed) :
    Var targetContext.sigs sig :=
  let wire :=
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
      value
  let member :=
    InsertionCompilation.NaturalityInternal.origin_member source.val
      sourceContext.ids value
  let targetMember :=
    target_visible source removed correspond wire survives member
  InsertionCompilation.NaturalityInternal.castVar
    ((targetWire_signature source removed wire survives).trans
      (ConcreteElaboration.WireContext.origin_signature source.val
        sourceContext.ids value))
    (InsertionCompilation.NaturalityInternal.varForMember
      (Target source removed)
      targetContext.ids (targetWire source removed wire survives)
      targetMember)

theorem survivingProjection_action
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    {sig : Sig}
    (value : Var sourceContext.sigs sig)
    (survives :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        removed) :
    ConcreteElaboration.WireContext.origin (Target source removed)
        targetContext.ids
        (survivingProjection source removed targetContext sourceContext
          correspond value survives) =
      targetWire source removed
        (ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids value) survives := by
  let wire :=
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
      value
  let member :=
    InsertionCompilation.NaturalityInternal.origin_member source.val
      sourceContext.ids value
  let targetMember :=
    target_visible source removed correspond wire survives member
  have castOrigin :=
    InsertionCompilation.NaturalityInternal.origin_castVar
      (Target source removed) targetContext.ids
      ((targetWire_signature source removed wire survives).trans
        (ConcreteElaboration.WireContext.origin_signature source.val
          sourceContext.ids value))
      (InsertionCompilation.NaturalityInternal.varForMember
        (Target source removed) targetContext.ids
        (targetWire source removed wire survives) targetMember)
  have memberOrigin :=
    InsertionCompilation.NaturalityInternal.varForMember_origin
      (Target source removed) targetContext.ids
      (targetWire source removed wire survives) targetMember
  simpa only [survivingProjection, wire, member, targetMember] using
    castOrigin.trans memberOrigin

theorem contextProjection_action
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    ConcreteElaboration.WireContext.origin (Target source removed)
        targetContext.ids
        (contextProjection source removed targetContext sourceContext
          correspond removedAbsent value) =
      targetWire source removed
        (ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids value)
        (fun same =>
          removedAbsent (same ▸
            InsertionCompilation.NaturalityInternal.origin_member
              source.val sourceContext.ids value)) := by
  let wire :=
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
      value
  let member :=
    InsertionCompilation.NaturalityInternal.origin_member source.val
      sourceContext.ids value
  let survives : wire ≠ removed :=
    fun same => removedAbsent (same ▸ member)
  let targetMember :=
    target_visible source removed correspond wire survives member
  have castOrigin :=
    InsertionCompilation.NaturalityInternal.origin_castVar
      (Target source removed) targetContext.ids
      ((targetWire_signature source removed wire survives).trans
        (ConcreteElaboration.WireContext.origin_signature source.val
          sourceContext.ids value))
      (InsertionCompilation.NaturalityInternal.varForMember
        (Target source removed) targetContext.ids
        (targetWire source removed wire survives) targetMember)
  have memberOrigin :=
    InsertionCompilation.NaturalityInternal.varForMember_origin
      (Target source removed) targetContext.ids
      (targetWire source removed wire survives) targetMember
  simpa only [contextProjection, wire, member, survives, targetMember] using
    castOrigin.trans memberOrigin

theorem contextProjection_reindexed_identity
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids) :
    (fun {sig} (value : Var sourceContext.sigs sig) =>
      corresponding_sigs_eq source removed targetContext sourceContext
          correspond removedAbsent ▸
        contextProjection source removed targetContext sourceContext
          correspond removedAbsent value) =
      (fun {_} (value : Var sourceContext.sigs _) => value) := by
  funext sig value
  apply InsertionCompilation.NaturalityInternal.origin_injective
    source.val sourceContext.ids sourceNodup
  rw [cast_corresponding_origin source removed targetContext sourceContext
      correspond removedAbsent,
    contextProjection_action]
  simp

theorem sourceWire_injective
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    Function.Injective (sourceWire source removed) := by
  intro left right same
  calc
    left =
        targetWire source removed (sourceWire source removed left)
          (sourceWire_ne source removed left) :=
      (targetWire_sourceWire source removed left).symm
    _ =
        targetWire source removed (sourceWire source removed right)
          (sourceWire_ne source removed right) := by
      congr
    _ = right := targetWire_sourceWire source removed right

private theorem targetWire_congr
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    {left right : source.val.WireId}
    (same : left = right)
    (leftSurvives : left ≠ removed)
    (rightSurvives : right ≠ removed) :
    targetWire source removed left leftSurvives =
      targetWire source removed right rightSurvives := by
  subst right
  rfl

theorem Internal.targetContext_nodup
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup) :
    targetContext.ids.Nodup := by
  have mappedNodup :
      (targetContext.ids.map (sourceWire source removed)).Nodup := by
    rw [correspond]
    exact sourceNodup.filter _
  generalize targetContext.ids = ids at mappedNodup ⊢
  revert mappedNodup
  induction ids with
  | nil => simp
  | cons head tail induction =>
      intro mappedNodup
      rw [List.map_cons, List.nodup_cons] at mappedNodup
      rw [List.nodup_cons]
      refine ⟨?_, induction mappedNodup.2⟩
      intro member
      exact mappedNodup.1 (List.mem_map.mpr ⟨_, member, rfl⟩)

/-- A corresponding copied context remains strictly above the copied region. -/
theorem contextAbove_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (above :
      ConcreteElaboration.ContextAbove source.val sourceContext region) :
    ConcreteElaboration.ContextAbove (Target source removed) targetContext
      (targetRegion source removed region) := by
  constructor
  · exact targetContext_nodup source removed targetContext sourceContext
      correspond above.1
  · intro targetWireId targetMember
    have sourceMember :=
      source_visible source removed correspond targetWireId targetMember
    obtain ⟨steps, positive, climbed⟩ :=
      above.2 (sourceWire source removed targetWireId) sourceMember
    refine ⟨steps, positive, ?_⟩
    rw [targetRegion_climb]
    rw [climbed]
    simpa using
      (targetWire_scope source removed
        (sourceWire source removed targetWireId)
        (sourceWire_ne source removed targetWireId)).symm

theorem contextProjection_embedding
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    contextProjection source removed targetContext sourceContext correspond
        removedAbsent
        (contextEmbedding source removed targetContext sourceContext
          correspond value) =
      value := by
  apply InsertionCompilation.NaturalityInternal.origin_injective
    (Target source removed) targetContext.ids
  · exact targetContext_nodup source removed targetContext sourceContext
      correspond sourceNodup
  · rw [contextProjection_action]
    have sourceOrigin :=
      contextEmbedding_action source removed targetContext sourceContext
        correspond value
    calc
      _ =
          targetWire source removed
            (sourceWire source removed
              (ConcreteElaboration.WireContext.origin
                (Target source removed) targetContext.ids value))
            (sourceWire_ne source removed
              (ConcreteElaboration.WireContext.origin
                (Target source removed) targetContext.ids value)) := by
        congr
      _ = _ := targetWire_sourceWire source removed _

theorem survivingProjection_embedding
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    survivingProjection source removed targetContext sourceContext correspond
        (contextEmbedding source removed targetContext sourceContext
          correspond value)
        (by
          rw [contextEmbedding_action]
          exact sourceWire_ne source removed _) =
      value := by
  apply InsertionCompilation.NaturalityInternal.origin_injective
    (Target source removed) targetContext.ids
  · exact targetContext_nodup source removed targetContext sourceContext
      correspond sourceNodup
  · rw [survivingProjection_action]
    have sourceOrigin :=
      contextEmbedding_action source removed targetContext sourceContext
        correspond value
    calc
      _ =
          targetWire source removed
            (sourceWire source removed
              (ConcreteElaboration.WireContext.origin
                (Target source removed) targetContext.ids value))
            (sourceWire_ne source removed
              (ConcreteElaboration.WireContext.origin
                (Target source removed) targetContext.ids value)) := by
        congr
      _ = _ := targetWire_sourceWire source removed _

theorem contextEmbedding_survivingProjection
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    {sig : Sig}
    (value : Var sourceContext.sigs sig)
    (survives :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        removed) :
    contextEmbedding source removed targetContext sourceContext correspond
        (survivingProjection source removed targetContext sourceContext
          correspond value survives) =
      value := by
  apply InsertionCompilation.NaturalityInternal.origin_injective source.val
    sourceContext.ids sourceNodup
  rw [contextEmbedding_action, survivingProjection_action]
  exact sourceWire_targetWire source removed _ survives

/--
Extend a target environment across the one deleted source variable.  Surviving
variables are read through the canonical projection and every occurrence of
the removed origin receives the caller-selected value.
-/
noncomputable def sourceEnvironmentFromTarget
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetEnv : Env pre targetContext.sigs) :
    Env pre sourceContext.sigs :=
  fun sig value =>
    if survives :
        ConcreteElaboration.WireContext.origin source.val sourceContext.ids
            value ≠
          removed
    then
      targetEnv sig
        (survivingProjection source removed targetContext sourceContext
          correspond value survives)
    else
      let originExact :
          ConcreteElaboration.WireContext.origin source.val sourceContext.ids
              value =
            removed :=
        Classical.not_not.mp survives
      let signature :
          (source.val.wires removed).sig = sig :=
        (congrArg (fun wire => (source.val.wires wire).sig)
            originExact).symm.trans
          (ConcreteElaboration.WireContext.origin_signature source.val
            sourceContext.ids value)
      congrArg pre.Domain signature ▸ specified

theorem sourceEnvironmentFromTarget_embedding
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetEnv : Env pre targetContext.sigs) :
    Env.comp
        (sourceEnvironmentFromTarget source removed targetContext
          sourceContext correspond pre specified targetEnv)
        (contextEmbedding source removed targetContext sourceContext
          correspond) =
      targetEnv := by
  funext sig value
  simp only [Env.comp, sourceEnvironmentFromTarget]
  split
  · rename_i survives
    exact congrArg (targetEnv sig)
      (survivingProjection_embedding source removed targetContext
        sourceContext correspond sourceNodup value)
  · rename_i notSurvives
    exact (notSurvives (by
      rw [contextEmbedding_action]
      exact sourceWire_ne source removed _)).elim

theorem sourceEnvironmentFromTarget_removed
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetEnv : Env pre targetContext.sigs)
    (value : Var sourceContext.sigs (source.val.wires removed).sig)
    (origin :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value =
        removed) :
    sourceEnvironmentFromTarget source removed targetContext sourceContext
        correspond pre specified targetEnv _ value =
      specified := by
  simp only [sourceEnvironmentFromTarget]
  split
  · rename_i survives
    exact (survives origin).elim
  · rfl

/-- The exact semantic relation between paired deletion environments. -/
structure EnvironmentsCorrespond
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetEnv : Env pre targetContext.sigs)
    (sourceEnv : Env pre sourceContext.sigs) : Prop where
  surviving :
    Env.comp sourceEnv
        (contextEmbedding source removed targetContext sourceContext
          correspond) =
      targetEnv
  removedValue :
    ∀ value : Var sourceContext.sigs (source.val.wires removed).sig,
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value =
        removed →
      sourceEnv _ value = specified

theorem sourceEnvironmentFromTarget_corresponds
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetEnv : Env pre targetContext.sigs) :
    EnvironmentsCorrespond source removed targetContext sourceContext
      correspond pre specified targetEnv
      (sourceEnvironmentFromTarget source removed targetContext
        sourceContext correspond pre specified targetEnv) where
  surviving :=
    sourceEnvironmentFromTarget_embedding source removed targetContext
      sourceContext correspond sourceNodup pre specified targetEnv
  removedValue :=
    sourceEnvironmentFromTarget_removed source removed targetContext
      sourceContext correspond pre specified targetEnv

/--
The correspondence relation has one source environment: the canonical
extension of the target environment by the specified removed-wire value.
-/
theorem EnvironmentsCorrespond.source_eq
    {source : CheckedDiagram definitions}
    {removed : source.val.WireId}
    {targetContext :
      ConcreteElaboration.WireContext (Target source removed)}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {correspond :
      ContextsCorrespond source removed targetContext sourceContext}
    {pre : PreModel.{u}}
    {specified : pre.Domain (source.val.wires removed).sig}
    {targetEnv : Env pre targetContext.sigs}
    {sourceEnv : Env pre sourceContext.sigs}
    (environments :
      EnvironmentsCorrespond source removed targetContext sourceContext
        correspond pre specified targetEnv sourceEnv)
    (sourceNodup : sourceContext.ids.Nodup) :
    sourceEnv =
      sourceEnvironmentFromTarget source removed targetContext sourceContext
        correspond pre specified targetEnv := by
  funext sig value
  by_cases survives :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        removed
  · have survivingExact :=
      congrFun (congrFun environments.surviving sig)
        (survivingProjection source removed targetContext sourceContext
          correspond value survives)
    change
      sourceEnv sig
          (contextEmbedding source removed targetContext sourceContext
            correspond
            (survivingProjection source removed targetContext sourceContext
              correspond value survives)) =
        _ at survivingExact
    rw [contextEmbedding_survivingProjection source removed targetContext
      sourceContext correspond sourceNodup value survives] at survivingExact
    simpa [sourceEnvironmentFromTarget, survives] using survivingExact
  · have originExact :
        ConcreteElaboration.WireContext.origin source.val sourceContext.ids
            value =
          removed :=
      Classical.not_not.mp survives
    have signature :
        (source.val.wires removed).sig = sig :=
      (congrArg (fun wire => (source.val.wires wire).sig)
          originExact).symm.trans
        (ConcreteElaboration.WireContext.origin_signature source.val
          sourceContext.ids value)
    cases signature
    rw [environments.removedValue value originExact]
    exact
      (sourceEnvironmentFromTarget_removed source removed targetContext
        sourceContext correspond pre specified targetEnv value
        originExact).symm

theorem contextProjection_embedding_environment
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids)
    (pre : PreModel)
    (targetEnv : Env pre targetContext.sigs) :
    Env.comp
        (Env.comp targetEnv
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        (contextEmbedding source removed targetContext sourceContext
          correspond) =
      targetEnv := by
  funext sig value
  exact congrArg (targetEnv sig)
    (contextProjection_embedding source removed targetContext sourceContext
      correspond sourceNodup removedAbsent value)

theorem contextEmbedding_projection
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    contextEmbedding source removed targetContext sourceContext correspond
        (contextProjection source removed targetContext sourceContext
          correspond removedAbsent value) =
      value := by
  apply InsertionCompilation.NaturalityInternal.origin_injective source.val
    sourceContext.ids sourceNodup
  rw [contextEmbedding_action, contextProjection_action]
  simp

theorem contextEmbedding_projection_environment
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids)
    (pre : PreModel)
    (sourceEnv : Env pre sourceContext.sigs) :
    Env.comp
        (Env.comp sourceEnv
          (contextEmbedding source removed targetContext sourceContext
            correspond))
        (contextProjection source removed targetContext sourceContext
          correspond removedAbsent) =
      sourceEnv := by
  funext sig value
  exact congrArg (sourceEnv sig)
    (contextEmbedding_projection source removed targetContext sourceContext
      correspond sourceNodup removedAbsent value)

theorem removed_not_mem_wiresAt
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId)
    (notScope : region ≠ (source.val.wires removed).scope) :
    removed ∉ source.val.wiresAt region := by
  intro member
  apply notScope
  have scopeEq :
      (source.val.wires removed).scope = region := by
    simpa [ConcreteDiagram.wiresAt] using (List.mem_filter.mp member).2
  exact scopeEq.symm

theorem retainedLocalSigs_eq
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region : source.val.RegionId)
    (notScope : region ≠ (source.val.wires removed).scope) :
    ((Target source removed).wiresAt
        (targetRegion source removed region)).map
          (fun wire => ((Target source removed).wires wire).sig) =
      (source.val.wiresAt region).map
        (fun wire => (source.val.wires wire).sig) := by
  rw [wiresAt_signatures]
  congr 1
  apply List.filter_eq_self.mpr
  intro wire member
  simp only [decide_eq_true_eq]
  intro same
  subst wire
  exact removed_not_mem_wiresAt source removed region notScope member

theorem removed_absent_extend
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (removedAbsent : removed ∉ sourceContext.ids)
    (notScope : region ≠ (source.val.wires removed).scope) :
    removed ∉ (sourceContext.extend region).ids := by
  simp only [ConcreteElaboration.WireContext.extend, List.mem_append,
    not_or]
  exact
    ⟨removed_not_mem_wiresAt source removed region notScope, removedAbsent⟩

private theorem contextEmbedding_appendRight
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    contextEmbedding source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        (ConcreteElaboration.appendRightVar (Target source removed)
          ((Target source removed).wiresAt
            (targetRegion source removed region)) value) =
      ConcreteElaboration.appendRightVar source.val
        (source.val.wiresAt region)
        (contextEmbedding source removed targetContext sourceContext
          correspond value) := by
  apply InsertionCompilation.NaturalityInternal.origin_injective source.val
    (sourceContext.extend region).ids sourceExtendedNodup
  rw [contextEmbedding_action]
  change
    sourceWire source removed
        (ConcreteElaboration.WireContext.origin (Target source removed)
          (((Target source removed).wiresAt
            (targetRegion source removed region)) ++ targetContext.ids)
          (ConcreteElaboration.appendRightVar (Target source removed)
            ((Target source removed).wiresAt
              (targetRegion source removed region)) value)) =
      ConcreteElaboration.WireContext.origin source.val
        ((source.val.wiresAt region) ++ sourceContext.ids)
        (ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region)
          (contextEmbedding source removed targetContext sourceContext
            correspond value))
  rw [ConcreteElaboration.origin_appendRightVar,
    ConcreteElaboration.origin_appendRightVar]
  rw [contextEmbedding_action]

private theorem contextProjection_appendRight
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids)
    (notScope : region ≠ (source.val.wires removed).scope)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    contextProjection source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        (removed_absent_extend source removed sourceContext region
          removedAbsent notScope)
        (ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region) value) =
      ConcreteElaboration.appendRightVar (Target source removed)
        ((Target source removed).wiresAt
          (targetRegion source removed region))
        (contextProjection source removed targetContext sourceContext
          correspond removedAbsent value) := by
  apply InsertionCompilation.NaturalityInternal.origin_injective
    (Target source removed)
    (targetContext.extend (targetRegion source removed region)).ids
  · exact
      targetContext_nodup source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        sourceExtendedNodup
  · rw [contextProjection_action]
    change
      targetWire source removed
          (ConcreteElaboration.WireContext.origin source.val
            ((source.val.wiresAt region) ++ sourceContext.ids)
            (ConcreteElaboration.appendRightVar source.val
              (source.val.wiresAt region) value)) _ =
        ConcreteElaboration.WireContext.origin (Target source removed)
          (((Target source removed).wiresAt
            (targetRegion source removed region)) ++ targetContext.ids)
          (ConcreteElaboration.appendRightVar (Target source removed)
            ((Target source removed).wiresAt
              (targetRegion source removed region))
            (contextProjection source removed targetContext sourceContext
              correspond removedAbsent value))
    calc
      _ =
          targetWire source removed
            (ConcreteElaboration.WireContext.origin source.val
              sourceContext.ids value) _ := by
        exact targetWire_congr source removed
          (ConcreteElaboration.origin_appendRightVar source.val
            (source.val.wiresAt region) value) _ _
      _ =
          ConcreteElaboration.WireContext.origin (Target source removed)
            targetContext.ids
            (contextProjection source removed targetContext sourceContext
              correspond removedAbsent value) :=
        (contextProjection_action source removed targetContext sourceContext
          correspond removedAbsent value).symm
      _ = _ :=
        (ConcreteElaboration.origin_appendRightVar
          (Target source removed)
          ((Target source removed).wiresAt
            (targetRegion source removed region))
        (contextProjection source removed targetContext sourceContext
          correspond removedAbsent value)).symm

theorem Internal.survivingProjection_appendRight
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    {sig : Sig}
    (value : Var sourceContext.sigs sig)
    (survives :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        removed) :
    survivingProjection source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        (ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region) value)
        (by
          intro same
          apply survives
          exact
            (ConcreteElaboration.origin_appendRightVar source.val
              (source.val.wiresAt region) value).symm.trans same) =
      ConcreteElaboration.appendRightVar (Target source removed)
        ((Target source removed).wiresAt
          (targetRegion source removed region))
        (survivingProjection source removed targetContext sourceContext
          correspond value survives) := by
  apply InsertionCompilation.NaturalityInternal.origin_injective
    (Target source removed)
    (targetContext.extend (targetRegion source removed region)).ids
  · exact
      targetContext_nodup source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        sourceExtendedNodup
  · let extendedValue :=
      ConcreteElaboration.appendRightVar source.val
        (source.val.wiresAt region) value
    have sourceOrigin :
        ConcreteElaboration.WireContext.origin source.val
            (sourceContext.extend region).ids extendedValue =
          ConcreteElaboration.WireContext.origin source.val
            sourceContext.ids value := by
      exact
        ConcreteElaboration.origin_appendRightVar source.val
          (source.val.wiresAt region) value
    let extendedSurvives :
        ConcreteElaboration.WireContext.origin source.val
            (sourceContext.extend region).ids extendedValue ≠
          removed :=
      fun same => survives (sourceOrigin.symm.trans same)
    calc
      ConcreteElaboration.WireContext.origin (Target source removed)
          (targetContext.extend (targetRegion source removed region)).ids
          (survivingProjection source removed
            (targetContext.extend (targetRegion source removed region))
            (sourceContext.extend region)
            (extend_contexts_correspond source removed correspond region)
            extendedValue extendedSurvives) =
        targetWire source removed
          (ConcreteElaboration.WireContext.origin source.val
            (sourceContext.extend region).ids extendedValue)
          extendedSurvives :=
        survivingProjection_action source removed
          (targetContext.extend (targetRegion source removed region))
          (sourceContext.extend region)
          (extend_contexts_correspond source removed correspond region)
          extendedValue extendedSurvives
      _ =
        targetWire source removed
          (ConcreteElaboration.WireContext.origin source.val
            sourceContext.ids value) survives :=
        targetWire_congr source removed sourceOrigin extendedSurvives
          survives
      _ =
        ConcreteElaboration.WireContext.origin (Target source removed)
          targetContext.ids
          (survivingProjection source removed targetContext sourceContext
            correspond value survives) :=
        (survivingProjection_action source removed targetContext
          sourceContext correspond value survives).symm
      _ =
        ConcreteElaboration.WireContext.origin (Target source removed)
          (targetContext.extend (targetRegion source removed region)).ids
          (ConcreteElaboration.appendRightVar (Target source removed)
            ((Target source removed).wiresAt
              (targetRegion source removed region))
            (survivingProjection source removed targetContext sourceContext
              correspond value survives)) :=
        (ConcreteElaboration.origin_appendRightVar
          (Target source removed)
          ((Target source removed).wiresAt
            (targetRegion source removed region))
          (survivingProjection source removed targetContext sourceContext
            correspond value survives)).symm

theorem Internal.extendEnvironment_from
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (env : Env pre (context.extend region).sigs)
    (outerEnv : Env pre context.sigs)
    (agrees : ∀ {sig} (value : Var context.sigs sig),
      env sig
          (ConcreteElaboration.appendRightVar diagram
            (diagram.wiresAt region) value) =
        outerEnv sig value) :
    ConcreteElaboration.extendEnvironment diagram context region
        (ConcreteElaboration.valuesFromEnvironmentFor diagram context.ids
          (diagram.wiresAt region) env)
        outerEnv =
      env := by
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig value
  exact agrees value

/--
Extend a paired environment through one retained region in the
target-to-source direction.  A removed value already living in the source
outer environment is preserved; all local wires survive because this is not
the removed wire's own scope.
-/
theorem Internal.extendEnvironmentsCorrespond_target
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (notScope : region ≠ (source.val.wires removed).scope)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetOuter : Env pre targetContext.sigs)
    (sourceOuter : Env pre sourceContext.sigs)
    (outerCorrespond :
      EnvironmentsCorrespond source removed targetContext sourceContext
        correspond pre specified targetOuter sourceOuter)
    (targetValues :
      ConcreteElaboration.WireValues pre
        (((Target source removed).wiresAt
          (targetRegion source removed region)).map fun wire =>
            ((Target source removed).wires wire).sig)) :
    ∃ sourceValues :
        ConcreteElaboration.WireValues pre
          ((source.val.wiresAt region).map fun wire =>
            (source.val.wires wire).sig),
      EnvironmentsCorrespond source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        pre specified
        (ConcreteElaboration.extendEnvironment (Target source removed)
          targetContext (targetRegion source removed region)
          targetValues targetOuter)
        (ConcreteElaboration.extendEnvironment source.val sourceContext
          region sourceValues sourceOuter) := by
  let targetExtended :=
    ConcreteElaboration.extendEnvironment (Target source removed)
      targetContext (targetRegion source removed region)
      targetValues targetOuter
  let extendedCorrespond :=
    extend_contexts_correspond source removed correspond region
  let sourceCandidate :=
    sourceEnvironmentFromTarget source removed
      (targetContext.extend (targetRegion source removed region))
      (sourceContext.extend region) extendedCorrespond pre specified
      targetExtended
  let sourceValues :=
    ConcreteElaboration.valuesFromEnvironmentFor source.val
      sourceContext.ids (source.val.wiresAt region) sourceCandidate
  refine ⟨sourceValues, ?_⟩
  have sourceRealized :
      ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceOuter =
        sourceCandidate := by
    apply extendEnvironment_from
    intro sig value
    change
      sourceCandidate sig
          (ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) value) =
        sourceOuter sig value
    simp only [sourceCandidate, sourceEnvironmentFromTarget]
    split
    · rename_i survives
      have outerSurvives :
          ConcreteElaboration.WireContext.origin source.val sourceContext.ids
              value ≠
            removed := by
        intro same
        apply survives
        exact
          (ConcreteElaboration.origin_appendRightVar source.val
            (source.val.wiresAt region) value).trans same
      rw [survivingProjection_appendRight source removed targetContext
        sourceContext correspond region sourceExtendedNodup value
        outerSurvives]
      dsimp [targetExtended]
      rw [ConcreteElaboration.extendEnvironment_appendRightVar]
      have outerPoint :=
        congrFun (congrFun outerCorrespond.surviving sig)
          (survivingProjection source removed targetContext sourceContext
            correspond value outerSurvives)
      have embeddedExact :=
        contextEmbedding_survivingProjection source removed targetContext
          sourceContext correspond
          (by
            have parts := sourceExtendedNodup
            rw [ConcreteElaboration.WireContext.extend,
              List.nodup_append] at parts
            exact parts.2.1)
          value outerSurvives
      simpa only [Env.comp, embeddedExact] using outerPoint.symm
    · rename_i notSurvives
      have outerOrigin :
          ConcreteElaboration.WireContext.origin source.val sourceContext.ids
              value =
            removed := by
        apply Classical.not_not.mp
        intro outerSurvives
        exact notSurvives (by
          intro same
          apply outerSurvives
          exact
            (ConcreteElaboration.origin_appendRightVar source.val
              (source.val.wiresAt region) value).symm.trans same)
      have signature :
          (source.val.wires removed).sig = sig :=
        (congrArg (fun wire => (source.val.wires wire).sig)
            outerOrigin).symm.trans
          (ConcreteElaboration.WireContext.origin_signature source.val
            sourceContext.ids value)
      cases signature
      exact (outerCorrespond.removedValue value outerOrigin).symm
  rw [sourceRealized]
  exact
    sourceEnvironmentFromTarget_corresponds source removed
      (targetContext.extend (targetRegion source removed region))
      (sourceContext.extend region) extendedCorrespond sourceExtendedNodup
      pre specified targetExtended

/-- Extend a paired environment through one retained region source-to-target. -/
theorem Internal.extendEnvironmentsCorrespond_source
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (notScope : region ≠ (source.val.wires removed).scope)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetOuter : Env pre targetContext.sigs)
    (sourceOuter : Env pre sourceContext.sigs)
    (outerCorrespond :
      EnvironmentsCorrespond source removed targetContext sourceContext
        correspond pre specified targetOuter sourceOuter)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((source.val.wiresAt region).map fun wire =>
          (source.val.wires wire).sig)) :
    ∃ targetValues :
        ConcreteElaboration.WireValues pre
          (((Target source removed).wiresAt
            (targetRegion source removed region)).map fun wire =>
              ((Target source removed).wires wire).sig),
      EnvironmentsCorrespond source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        pre specified
        (ConcreteElaboration.extendEnvironment (Target source removed)
          targetContext (targetRegion source removed region)
          targetValues targetOuter)
        (ConcreteElaboration.extendEnvironment source.val sourceContext
          region sourceValues sourceOuter) := by
  let sourceExtended :=
    ConcreteElaboration.extendEnvironment source.val sourceContext region
      sourceValues sourceOuter
  let extendedCorrespond :=
    extend_contexts_correspond source removed correspond region
  let targetCandidate :=
    Env.comp sourceExtended
      (contextEmbedding source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region) extendedCorrespond)
  let targetValues :=
    ConcreteElaboration.valuesFromEnvironmentFor
      (Target source removed) targetContext.ids
      ((Target source removed).wiresAt
        (targetRegion source removed region))
      targetCandidate
  refine ⟨targetValues, ?_⟩
  have targetRealized :
      ConcreteElaboration.extendEnvironment (Target source removed)
          targetContext (targetRegion source removed region)
          targetValues targetOuter =
        targetCandidate := by
    apply extendEnvironment_from
    intro sig value
    change
      sourceExtended sig
          (contextEmbedding source removed
            (targetContext.extend (targetRegion source removed region))
            (sourceContext.extend region) extendedCorrespond
            (ConcreteElaboration.appendRightVar (Target source removed)
              ((Target source removed).wiresAt
                (targetRegion source removed region)) value)) =
        targetOuter sig value
    rw [contextEmbedding_appendRight source removed targetContext
      sourceContext correspond region sourceExtendedNodup]
    dsimp [sourceExtended]
    rw [ConcreteElaboration.extendEnvironment_appendRightVar]
    exact congrFun (congrFun outerCorrespond.surviving sig) value
  rw [targetRealized]
  refine
    { surviving := rfl
      removedValue := ?_ }
  intro value origin
  have outerMember : removed ∈ sourceContext.ids := by
    have member :=
      InsertionCompilation.NaturalityInternal.origin_member source.val
        (sourceContext.extend region).ids value
    rw [origin, ConcreteElaboration.WireContext.extend,
      List.mem_append] at member
    exact member.resolve_left
      (removed_not_mem_wiresAt source removed region notScope)
  let outerValue :=
    InsertionCompilation.NaturalityInternal.varForMember source.val
      sourceContext.ids removed outerMember
  have outerOrigin :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          outerValue =
        removed :=
    InsertionCompilation.NaturalityInternal.varForMember_origin source.val
      sourceContext.ids removed outerMember
  have appendedExact :
      ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region) outerValue =
        value := by
    apply InsertionCompilation.NaturalityInternal.origin_injective source.val
      (sourceContext.extend region).ids sourceExtendedNodup
    calc
      ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend region).ids
          (ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) outerValue) =
        ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids outerValue :=
        ConcreteElaboration.origin_appendRightVar source.val
          (source.val.wiresAt region) outerValue
      _ = removed := outerOrigin
      _ =
        ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend region).ids value := origin.symm
  rw [← appendedExact]
  change
    ConcreteElaboration.extendEnvironment source.val sourceContext region
        sourceValues sourceOuter _ _ =
      specified
  rw [ConcreteElaboration.extendEnvironment_appendRightVar]
  exact outerCorrespond.removedValue outerValue outerOrigin

/--
At the removed wire's own scope, recover its bound value from the source
locals and delete exactly that local coordinate. The retained target locals
and the resulting full environments are canonical.
-/
theorem Internal.dyingScopeEnvironmentsCorrespond_source
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    (sourceExtendedNodup :
      (sourceContext.extend (source.val.wires removed).scope).ids.Nodup)
    (pre : PreModel.{u})
    (targetOuter : Env pre targetContext.sigs)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((source.val.wiresAt (source.val.wires removed).scope).map
          fun wire => (source.val.wires wire).sig)) :
    ∃ (specified : pre.Domain (source.val.wires removed).sig)
      (targetValues :
        ConcreteElaboration.WireValues pre
          (((Target source removed).wiresAt
            (targetRegion source removed
              (source.val.wires removed).scope)).map
            fun wire => ((Target source removed).wires wire).sig)),
      EnvironmentsCorrespond source removed
        (targetContext.extend
          (targetRegion source removed
            (source.val.wires removed).scope))
        (sourceContext.extend (source.val.wires removed).scope)
        (extend_contexts_correspond source removed correspond
          (source.val.wires removed).scope)
        pre specified
        (ConcreteElaboration.extendEnvironment (Target source removed)
          targetContext
          (targetRegion source removed
            (source.val.wires removed).scope)
          targetValues targetOuter)
        (ConcreteElaboration.extendEnvironment source.val sourceContext
          (source.val.wires removed).scope sourceValues
          (Env.comp targetOuter
            (contextProjection source removed targetContext sourceContext
              correspond removedAbsent))) := by
  let region := (source.val.wires removed).scope
  have removedMember : removed ∈ source.val.wiresAt region := by
    simp [region, ConcreteDiagram.wiresAt, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin]
  have removedExtendedMember :
      removed ∈ (sourceContext.extend region).ids := by
    simp [ConcreteElaboration.WireContext.extend, removedMember]
  let removedVariable :
      Var
        (sourceContext.extend region).sigs
        (source.val.wires removed).sig :=
    InsertionCompilation.NaturalityInternal.varForMember source.val
      (sourceContext.extend region).ids removed removedExtendedMember
  have removedVariableOrigin :
      ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend region).ids removedVariable =
        removed :=
    InsertionCompilation.NaturalityInternal.varForMember_origin source.val
      (sourceContext.extend region).ids removed removedExtendedMember
  let sourceOuter :=
    Env.comp targetOuter
      (contextProjection source removed targetContext sourceContext
        correspond removedAbsent)
  let sourceExtended :=
    ConcreteElaboration.extendEnvironment source.val sourceContext region
      sourceValues sourceOuter
  let specified := sourceExtended _ removedVariable
  let extendedCorrespond :=
    extend_contexts_correspond source removed correspond region
  let targetExtended :=
    Env.comp sourceExtended
      (contextEmbedding source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region) extendedCorrespond)
  let targetValues :=
    ConcreteElaboration.valuesFromEnvironmentFor
      (Target source removed) targetContext.ids
      ((Target source removed).wiresAt
        (targetRegion source removed region))
      targetExtended
  refine ⟨specified, targetValues, ?_⟩
  have sourceNodup : sourceContext.ids.Nodup := by
    have parts := sourceExtendedNodup
    rw [ConcreteElaboration.WireContext.extend,
      List.nodup_append] at parts
    exact parts.2.1
  have targetRealized :
      ConcreteElaboration.extendEnvironment (Target source removed)
          targetContext (targetRegion source removed region)
          targetValues targetOuter =
        targetExtended := by
    apply extendEnvironment_from
    intro sig value
    change
      sourceExtended sig
          (contextEmbedding source removed
            (targetContext.extend (targetRegion source removed region))
            (sourceContext.extend region) extendedCorrespond
            (ConcreteElaboration.appendRightVar (Target source removed)
              ((Target source removed).wiresAt
                (targetRegion source removed region)) value)) =
        targetOuter sig value
    rw [show
      contextEmbedding source removed
          (targetContext.extend (targetRegion source removed region))
          (sourceContext.extend region) extendedCorrespond
          (ConcreteElaboration.appendRightVar (Target source removed)
            ((Target source removed).wiresAt
              (targetRegion source removed region)) value) =
        ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region)
          (contextEmbedding source removed targetContext sourceContext
            correspond value) by
      simpa [extendedCorrespond] using
        (contextEmbedding_appendRight source removed targetContext
          sourceContext correspond region sourceExtendedNodup value)]
    dsimp [sourceExtended]
    rw [ConcreteElaboration.extendEnvironment_appendRightVar]
    change
      targetOuter sig
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent
            (contextEmbedding source removed targetContext sourceContext
              correspond value)) =
        targetOuter sig value
    exact congrArg (targetOuter sig)
      (contextProjection_embedding source removed targetContext sourceContext
        correspond sourceNodup removedAbsent value)
  rw [targetRealized]
  refine
    { surviving := rfl
      removedValue := ?_ }
  intro value origin
  have removedExact : removedVariable = value := by
    apply InsertionCompilation.NaturalityInternal.origin_injective source.val
      (sourceContext.extend region).ids sourceExtendedNodup
    calc
      ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend region).ids removedVariable =
        removed := removedVariableOrigin
      _ =
        ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend region).ids value := origin.symm
  rw [← removedExact]

/--
Canonical retained local environments correspond in both directions above the
dying scope. Witnesses are reconstructed from the already-related extended
environment, so no positional cast or choice is introduced.
-/
theorem extendedEnvironment_correspondence
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids)
    (notScope : region ≠ (source.val.wires removed).scope)
    (pre : PreModel)
    (sourceOuter : Env pre sourceContext.sigs)
    (targetOuter : Env pre targetContext.sigs)
    (outerExact :
      sourceOuter =
        Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent)) :
    (∀ sourceValues :
        ConcreteElaboration.WireValues pre
          ((source.val.wiresAt region).map fun wire =>
            (source.val.wires wire).sig),
      ∃ targetValues :
          ConcreteElaboration.WireValues pre
            (((Target source removed).wiresAt
              (targetRegion source removed region)).map fun wire =>
                ((Target source removed).wires wire).sig),
        ConcreteElaboration.extendEnvironment source.val sourceContext region
            sourceValues sourceOuter =
          Env.comp
            (ConcreteElaboration.extendEnvironment
              (Target source removed) targetContext
              (targetRegion source removed region)
              targetValues targetOuter)
            (contextProjection source removed
              (targetContext.extend (targetRegion source removed region))
              (sourceContext.extend region)
              (extend_contexts_correspond source removed correspond region)
              (removed_absent_extend source removed sourceContext region
                removedAbsent notScope))) ∧
      (∀ targetValues :
          ConcreteElaboration.WireValues pre
            (((Target source removed).wiresAt
              (targetRegion source removed region)).map fun wire =>
                ((Target source removed).wires wire).sig),
        ∃ sourceValues :
            ConcreteElaboration.WireValues pre
              ((source.val.wiresAt region).map fun wire =>
                (source.val.wires wire).sig),
          ConcreteElaboration.extendEnvironment source.val sourceContext
              region sourceValues sourceOuter =
            Env.comp
              (ConcreteElaboration.extendEnvironment
                (Target source removed) targetContext
                (targetRegion source removed region)
                targetValues targetOuter)
              (contextProjection source removed
                (targetContext.extend (targetRegion source removed region))
                (sourceContext.extend region)
                (extend_contexts_correspond source removed correspond region)
                (removed_absent_extend source removed sourceContext region
                  removedAbsent notScope))) := by
  let targetExtendedContext :=
    targetContext.extend (targetRegion source removed region)
  let sourceExtendedContext := sourceContext.extend region
  let extendedCorrespond :=
    extend_contexts_correspond source removed correspond region
  let extendedAbsent :=
    removed_absent_extend source removed sourceContext region removedAbsent
      notScope
  let extendedProjection :=
    (fun {_} value =>
      contextProjection source removed targetExtendedContext
        sourceExtendedContext extendedCorrespond extendedAbsent value :
      WireRenaming sourceExtendedContext.sigs targetExtendedContext.sigs)
  let extendedEmbedding :=
    (fun {_} value =>
      contextEmbedding source removed targetExtendedContext
        sourceExtendedContext extendedCorrespond value :
      WireRenaming targetExtendedContext.sigs sourceExtendedContext.sigs)
  have sourceNodup : sourceContext.ids.Nodup := by
    have parts := sourceExtendedNodup
    rw [ConcreteElaboration.WireContext.extend,
      List.nodup_append] at parts
    exact parts.2.1
  constructor
  · intro sourceValues
    let sourceExtended :=
      ConcreteElaboration.extendEnvironment source.val sourceContext region
        sourceValues sourceOuter
    let targetExtended := Env.comp sourceExtended extendedEmbedding
    let targetValues :=
      ConcreteElaboration.valuesFromEnvironmentFor
        (Target source removed) targetContext.ids
        ((Target source removed).wiresAt
          (targetRegion source removed region))
        targetExtended
    refine ⟨targetValues, ?_⟩
    have targetRealized :
        ConcreteElaboration.extendEnvironment (Target source removed)
            targetContext (targetRegion source removed region)
            targetValues targetOuter =
          targetExtended := by
      apply extendEnvironment_from
      intro sig value
      change
        sourceExtended sig
            (extendedEmbedding
              (ConcreteElaboration.appendRightVar
                (Target source removed)
                ((Target source removed).wiresAt
                  (targetRegion source removed region)) value)) =
          targetOuter sig value
      rw [show
        extendedEmbedding
            (ConcreteElaboration.appendRightVar (Target source removed)
              ((Target source removed).wiresAt
                (targetRegion source removed region)) value) =
          ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region)
            (contextEmbedding source removed targetContext sourceContext
              correspond value) by
        simpa [extendedEmbedding, targetExtendedContext,
          sourceExtendedContext, extendedCorrespond] using
          (contextEmbedding_appendRight source removed targetContext
            sourceContext correspond region sourceExtendedNodup value)]
      dsimp [sourceExtended]
      rw [ConcreteElaboration.extendEnvironment_appendRightVar, outerExact]
      exact congrArg (targetOuter sig)
        (contextProjection_embedding source removed targetContext sourceContext
          correspond sourceNodup removedAbsent value)
    rw [targetRealized]
    change sourceExtended = Env.comp targetExtended extendedProjection
    simpa [targetExtended, extendedProjection, extendedEmbedding,
      targetExtendedContext, sourceExtendedContext, extendedCorrespond,
      extendedAbsent] using
      (contextEmbedding_projection_environment source removed
        targetExtendedContext sourceExtendedContext extendedCorrespond
        sourceExtendedNodup extendedAbsent pre sourceExtended).symm
  · intro targetValues
    let targetExtended :=
      ConcreteElaboration.extendEnvironment (Target source removed)
        targetContext (targetRegion source removed region)
        targetValues targetOuter
    let sourceExtended := Env.comp targetExtended extendedProjection
    let sourceValues :=
      ConcreteElaboration.valuesFromEnvironmentFor source.val
        sourceContext.ids (source.val.wiresAt region) sourceExtended
    refine ⟨sourceValues, ?_⟩
    change
      ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceOuter =
        sourceExtended
    apply extendEnvironment_from
    intro sig value
    change
      targetExtended sig
          (extendedProjection
            (ConcreteElaboration.appendRightVar source.val
              (source.val.wiresAt region) value)) =
        sourceOuter sig value
    rw [show
      extendedProjection
          (ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) value) =
        ConcreteElaboration.appendRightVar (Target source removed)
          ((Target source removed).wiresAt
            (targetRegion source removed region))
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent value) by
      exact contextProjection_appendRight source removed targetContext
        sourceContext correspond region sourceExtendedNodup removedAbsent
        notScope value]
    dsimp [targetExtended]
    rw [ConcreteElaboration.extendEnvironment_appendRightVar, outerExact]
    rfl

end ExhaustedWireRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
