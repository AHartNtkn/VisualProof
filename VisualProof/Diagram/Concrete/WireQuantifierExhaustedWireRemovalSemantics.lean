import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemoval
import VisualProof.Diagram.Concrete.Subgraph.Factorization
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrameSupport
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalitySupport
import VisualProof.Diagram.ContextZipper

namespace VisualProof

universe u v w

namespace ConcreteWireQuantifier

namespace ExhaustedWireRemovalSemantics

private abbrev Target
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :=
  ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate source removed

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

private def retainedNodes
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

private theorem target_visible
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

private theorem targetContext_nodup
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

private theorem extendEnvironment_from
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

/--
Close one retained ancestor binder block around a strict-above zipper. The
dying scope is excluded explicitly, so this constructor never crosses the
unequal local binder blocks that deletion changes.
-/
private def transportRenaming
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (rho : WireRenaming source' target') :
    WireRenaming source target :=
  fun {_} value => targetExact.symm ▸ rho (sourceExact ▸ value)

private theorem transportRenaming_reindexed_identity
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (rawTargetToSource : target' = source')
    (targetToSource : target = source)
    (rho : WireRenaming source' target')
    (rawIdentity :
      (fun {sig} (value : Var source' sig) =>
        rawTargetToSource ▸ rho value) =
        (fun {_} (value : Var source' _) => value)) :
    (fun {sig} (value : Var source sig) =>
      targetToSource ▸
        transportRenaming sourceExact targetExact rho value) =
      (fun {_} (value : Var source _) => value) := by
  cases sourceExact
  cases targetExact
  have proofExact : targetToSource = rawTargetToSource :=
    Subsingleton.elim _ _
  rw [proofExact]
  exact rawIdentity

private theorem envComp_transportRenaming
    {source source' target target' : List Sig}
    (sourceExact : source' = source)
    (targetExact : target' = target)
    (rho : WireRenaming source' target') :
    (fun (pre : PreModel.{u}) (env : Env pre target) =>
      sourceExact ▸ Env.comp (targetExact.symm ▸ env) rho) =
      (fun (pre : PreModel.{u}) (env : Env pre target) =>
        Env.comp env
          (transportRenaming sourceExact.symm targetExact.symm rho)) := by
  cases sourceExact
  cases targetExact
  rfl

private theorem cast_trans
    {α : Sort v} {motive : α → Sort w}
    {left middle right : α}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (value : motive left) :
    middleRight ▸ (leftMiddle ▸ value) =
      (leftMiddle.trans middleRight) ▸ value := by
  cases leftMiddle
  cases middleRight
  rfl

private theorem bindMany_reindexBound
    {leftBound rightBound outer hole : List Sig}
    (same : leftBound = rightBound)
    (inner :
      DiagramContext definitions hole (leftBound ++ outer)) :
    DiagramContext.bindMany leftBound inner =
      DiagramContext.bindMany rightBound
        ((congrArg (fun bound => bound ++ outer) same) ▸ inner) := by
  cases same
  rfl

noncomputable def retainedBindContextComposable
    {source : CheckedDiagram definitions}
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    (region : source.val.RegionId)
    (notScope : region ≠ (source.val.wires removed).scope)
    (above :
      ConcreteElaboration.ContextAbove source.val sourceContext region)
    (sourceInner :
      DiagramContext definitions sourceHole
        (sourceContext.extend region).sigs)
    (targetInner :
      DiagramContext definitions targetHole
        (targetContext.extend
          (targetRegion source removed region)).sigs)
    (holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole)
    (inner :
      DiagramContext.ComposableSemanticZipper sourceInner targetInner
        (fun _pre env =>
          Env.comp env
            (contextProjection source removed
              (targetContext.extend (targetRegion source removed region))
              (sourceContext.extend region)
              (extend_contexts_correspond source removed correspond region)
              (removed_absent_extend source removed sourceContext region
                removedAbsent notScope)))
        holeMap) :
    DiagramContext.ComposableSemanticZipper
      (bindContextFor source.val sourceContext.ids
        (source.val.wiresAt region) sourceInner)
      (bindContextFor (Target source removed) targetContext.ids
        ((Target source removed).wiresAt
          (targetRegion source removed region)) targetInner)
      (fun _pre env =>
        Env.comp env
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
      holeMap := by
  let bound :=
    (source.val.wiresAt region).map
      (fun wire => (source.val.wires wire).sig)
  let outerRenaming :=
    (fun {_} value =>
      contextProjection source removed targetContext sourceContext correspond
        removedAbsent value :
      WireRenaming sourceContext.sigs targetContext.sigs)
  let fullRenaming :=
    (fun {_} value =>
      contextProjection source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        (removed_absent_extend source removed sourceContext region
          removedAbsent notScope) value :
      WireRenaming (sourceContext.extend region).sigs
        (targetContext.extend (targetRegion source removed region)).sigs)
  let sourceExact :
      (sourceContext.extend region).sigs =
        bound ++ sourceContext.sigs :=
    @List.map_append _ _
      (fun wire => (source.val.wires wire).sig)
      (source.val.wiresAt region) sourceContext.ids
  let targetExact :
      (targetContext.extend
          (targetRegion source removed region)).sigs =
        bound ++ targetContext.sigs :=
    (@List.map_append _ _
      (fun wire => ((Target source removed).wires wire).sig)
      ((Target source removed).wiresAt
        (targetRegion source removed region))
      targetContext.ids).trans
      (congrArg (fun localSigs => localSigs ++ targetContext.sigs)
        (retainedLocalSigs_eq source removed region notScope))
  let canonicalFullRenaming :
      WireRenaming (bound ++ sourceContext.sigs)
        (bound ++ targetContext.sigs) :=
    transportRenaming sourceExact.symm targetExact.symm fullRenaming
  let outerTargetToSource :=
    corresponding_sigs_eq source removed targetContext sourceContext
      correspond removedAbsent
  let fullTargetToSource :=
    corresponding_sigs_eq source removed
      (targetContext.extend (targetRegion source removed region))
      (sourceContext.extend region)
      (extend_contexts_correspond source removed correspond region)
      (removed_absent_extend source removed sourceContext region
        removedAbsent notScope)
  let canonicalTargetToSource :
      bound ++ targetContext.sigs = bound ++ sourceContext.sigs :=
    congrArg (List.append bound) outerTargetToSource
  have sourceExtendedNodup :
      (sourceContext.extend region).ids.Nodup :=
    ConcreteElaboration.extend_nodup definitions source.val source.property
      sourceContext region above
  have outerNodup : sourceContext.ids.Nodup := by
    have parts := sourceExtendedNodup
    rw [ConcreteElaboration.WireContext.extend,
      List.nodup_append] at parts
    exact parts.2.1
  have rawFullIdentity :
      (fun {sig} (value : Var (sourceContext.extend region).sigs sig) =>
        fullTargetToSource ▸ fullRenaming value) =
        (fun {_}
          (value : Var (sourceContext.extend region).sigs _) => value) :=
    by
      simpa only [fullTargetToSource, fullRenaming] using
        (contextProjection_reindexed_identity source removed
          (targetContext.extend (targetRegion source removed region))
          (sourceContext.extend region)
          (extend_contexts_correspond source removed correspond region)
          sourceExtendedNodup
          (removed_absent_extend source removed sourceContext region
            removedAbsent notScope))
  have outerIdentity :
      (fun {sig} (value : Var sourceContext.sigs sig) =>
        outerTargetToSource ▸ outerRenaming value) =
        (fun {_} (value : Var sourceContext.sigs _) => value) :=
    by
      simpa only [outerTargetToSource, outerRenaming] using
        (contextProjection_reindexed_identity source removed targetContext
          sourceContext correspond outerNodup removedAbsent)
  have canonicalFullIdentity :
      (fun {sig} (value : Var (bound ++ sourceContext.sigs) sig) =>
        canonicalTargetToSource ▸ canonicalFullRenaming value) =
        (fun {_}
          (value : Var (bound ++ sourceContext.sigs) _) => value) :=
    transportRenaming_reindexed_identity sourceExact.symm targetExact.symm
      fullTargetToSource canonicalTargetToSource fullRenaming
        rawFullIdentity
  have canonicalFullExact :
      (canonicalFullRenaming :
        WireRenaming (bound ++ sourceContext.sigs)
          (bound ++ targetContext.sigs)) =
        (DiagramContext.ComposableSemanticZipper.liftMany
          bound outerRenaming :
        WireRenaming (bound ++ sourceContext.sigs)
          (bound ++ targetContext.sigs)) :=
    by
      simpa only using
        (DiagramContext.ComposableSemanticZipper.eq_liftMany_of_reindexed_identity
          bound outerTargetToSource outerRenaming canonicalFullRenaming
            outerIdentity canonicalFullIdentity)
  have canonicalInnerRaw :=
    (inner.rebaseSourceOuter sourceExact).rebaseTargetOuter targetExact
  have canonicalInner :
      DiagramContext.ComposableSemanticZipper
        (sourceExact ▸ sourceInner) (targetExact ▸ targetInner)
        (fun (pre : PreModel.{u}) env =>
          Env.comp env canonicalFullRenaming)
        holeMap := by
    rw [← envComp_transportRenaming sourceExact targetExact fullRenaming]
    exact canonicalInnerRaw
  have liftedInner :
      DiagramContext.ComposableSemanticZipper
        (sourceExact ▸ sourceInner) (targetExact ▸ targetInner)
        (fun (pre : PreModel.{u}) env =>
          Env.comp env
            (DiagramContext.ComposableSemanticZipper.liftMany
              bound outerRenaming))
        holeMap := by
    rw [← canonicalFullExact]
    exact canonicalInner
  have boundComposable :=
    DiagramContext.ComposableSemanticZipper.bindMany
      bound outerRenaming liftedInner
  have sourceAncestorExact :
      bindContextFor source.val sourceContext.ids
          (source.val.wiresAt region) sourceInner =
        DiagramContext.bindMany bound (sourceExact ▸ sourceInner) := by
    rw [bindContextFor_eq_bindMany]
    unfold bound
    have proofExact :
        (@List.map_append _ _
            (fun wire => (source.val.wires wire).sig)
            (source.val.wiresAt region) sourceContext.ids) =
          sourceExact :=
      Subsingleton.elim _ _
    rw [proofExact]
    rfl
  have targetAncestorExact :
      bindContextFor (Target source removed) targetContext.ids
          ((Target source removed).wiresAt
            (targetRegion source removed region)) targetInner =
        DiagramContext.bindMany bound (targetExact ▸ targetInner) := by
    rw [bindContextFor_eq_bindMany]
    change
      DiagramContext.bindMany
          (((Target source removed).wiresAt
            (targetRegion source removed region)).map
              (fun wire => ((Target source removed).wires wire).sig))
          ((@List.map_append _ _
            (fun wire => ((Target source removed).wires wire).sig)
            ((Target source removed).wiresAt
              (targetRegion source removed region))
            targetContext.ids) ▸ targetInner) =
        DiagramContext.bindMany bound (targetExact ▸ targetInner)
    rw [bindMany_reindexBound
      (retainedLocalSigs_eq source removed region notScope)]
    apply congrArg (DiagramContext.bindMany bound)
    unfold bound
    let mapAppend :=
      @List.map_append _ _
        (fun wire => ((Target source removed).wires wire).sig)
        ((Target source removed).wiresAt
          (targetRegion source removed region))
        targetContext.ids
    let localExact :
        (((Target source removed).wiresAt
          (targetRegion source removed region)).map
            (fun wire => ((Target source removed).wires wire).sig)) ++
              targetContext.sigs =
          (source.val.wiresAt region).map
              (fun wire => (source.val.wires wire).sig) ++
                targetContext.sigs :=
      congrArg (fun localSigs => localSigs ++ targetContext.sigs)
        (retainedLocalSigs_eq source removed region notScope)
    calc
      _ = (mapAppend.trans localExact) ▸ targetInner := by
        exact cast_trans mapAppend localExact targetInner <;> rfl
      _ = targetExact ▸ targetInner := by
        have proofExact : mapAppend.trans localExact = targetExact :=
          Subsingleton.elim _ _
        rw [proofExact] <;> rfl
    all_goals rfl
  rw [sourceAncestorExact, targetAncestorExact]
  simpa only [outerRenaming] using boundComposable

private def targetEndpoint
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint (Target source removed).nodeCount :=
  ⟨targetNode source removed endpoint.node, endpoint.port⟩

private theorem targetEndpoint_incident
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : source.val.WireId)
    (survives : wire ≠ removed)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires wire).endpoints) :
    targetEndpoint source removed endpoint ∈
      ((Target source removed).wires
        (targetWire source removed wire survives)).endpoints := by
  unfold Target targetWire targetEndpoint targetNode retainedNodes
  simp only [
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate,
    DenseList.get_index]
  apply List.mem_filterMap.mpr
  refine ⟨endpoint, incident, ?_⟩
  split
  · rename_i retained
    congr 1
  · rename_i rejected
    exfalso
    apply rejected
    simp [ConcreteDiagram.nodesList, Data.Finite.mem_allFin]

theorem requiredPorts_sourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : (Target source removed).NodeId) :
    (Target source removed).requiredPorts node =
      source.val.requiredPorts (sourceNode source removed node) := by
  cases targetData : (Target source removed).nodes node <;>
    have shape := sourceNode_shape source removed node <;>
    simp only [targetData] at shape <;>
    simp [ConcreteDiagram.requiredPorts, targetData, shape]

private theorem required_owner_image
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    {targetContext :
      ConcreteElaboration.WireContext (Target source removed)}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (targetNodeId : (Target source removed).NodeId)
    (port : CPort)
    (sourceRequired :
      port ∈ source.val.requiredPorts
        (sourceNode source removed targetNodeId))
    (sourceOwnerWire : source.val.WireId)
    (sourceOwner : source.val.endpointOwner?
        ⟨sourceNode source removed targetNodeId, port⟩ =
      some sourceOwnerWire)
    (sourceMember : sourceOwnerWire ∈ sourceContext.ids) :
    ∃ targetWireId : (Target source removed).WireId,
      (Target source removed).endpointOwner?
          ⟨targetNodeId, port⟩ =
        some targetWireId ∧
      sourceWire source removed targetWireId = sourceOwnerWire ∧
      targetWireId ∈ targetContext.ids := by
  have sourceIncident :=
    ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode source removed targetNodeId, port⟩ sourceOwnerWire
      sourceOwner
  have survives : sourceOwnerWire ≠ removed := by
    intro same
    subst sourceOwnerWire
    rw [removedEndpoints] at sourceIncident
    simp at sourceIncident
  let targetWireId :=
    targetWire source removed sourceOwnerWire survives
  have targetIncident :
      (⟨targetNodeId, port⟩ :
        CEndpoint (Target source removed).nodeCount) ∈
        ((Target source removed).wires targetWireId).endpoints := by
    have mapped :=
      targetEndpoint_incident source removed sourceOwnerWire survives
        ⟨sourceNode source removed targetNodeId, port⟩ sourceIncident
    simpa [targetEndpoint, targetWireId] using mapped
  have targetRequired :
      port ∈ (Target source removed).requiredPorts targetNodeId := by
    rw [requiredPorts_sourceNode]
    exact sourceRequired
  have targetOwner :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions
      (Target source removed) targetWellFormed targetNodeId port
      targetRequired targetWireId targetIncident
  refine ⟨targetWireId, targetOwner, ?_, ?_⟩
  · exact sourceWire_targetWire source removed sourceOwnerWire survives
  · exact target_visible source removed correspond sourceOwnerWire survives
      sourceMember

private theorem compileNode_singleton_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (targetNodeId : (Target source removed).NodeId)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          [sourceNode source removed targetNodeId] =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      ConcreteElaboration.compileNodes? definitions
          (Target source removed) targetContext [targetNodeId] =
        some targetItems ∧
      sourceItems =
        targetItems.renameWires
          (contextEmbedding source removed targetContext sourceContext
            correspond) := by
  apply ConcreteElaboration.compileNodes?_singleton_reflect
    (target := Target source removed) (source := source.val)
    (targetContext := targetContext) (sourceContext := sourceContext)
    source.property sourceNodup
    (contextEmbedding source removed targetContext sourceContext correspond)
    (sourceWire source removed)
    (sourceWire_signature source removed)
    (contextEmbedding_action source removed targetContext sourceContext
      correspond)
    (sourceRegion source removed)
    targetNodeId (sourceNode source removed targetNodeId)
  · have copied :=
      targetNode_shape source removed
        (sourceNode source removed targetNodeId)
    rw [targetNode_sourceNode] at copied
    rw [copied]
    cases source.val.nodes
        (sourceNode source removed targetNodeId) <;> simp
  · intro port required sourceOwnerWire owner member
    exact required_owner_image source removed targetWellFormed
      removedEndpoints correspond targetNodeId port required
      sourceOwnerWire owner member
  · exact sourceCompiled

/-- Reflect an accepted ordered source node list without reordering it. -/
theorem compileNodes_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup) :
    ∀ (targetNodes : List (Target source removed).NodeId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          (targetNodes.map (sourceNode source removed)) =
        some sourceItems →
      ∃ targetItems : ItemSeq definitions targetContext.sigs,
        ConcreteElaboration.compileNodes? definitions
            (Target source removed) targetContext targetNodes =
          some targetItems ∧
        sourceItems =
          targetItems.renameWires
            (contextEmbedding source removed targetContext sourceContext
              correspond) := by
  intro targetNodes
  induction targetNodes with
  | nil =>
      intro sourceItems sourceCompiled
      have sourceEquality :
          (.nil : ItemSeq definitions sourceContext.sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using sourceCompiled)
      subst sourceItems
      exact ⟨.nil, rfl, rfl⟩
  | cons targetNodeId tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
          sourceTailCompiled, sourceItemsEquality⟩ :=
        InsertionCompilation.NaturalityInternal.compileNodes_cons_components
          definitions source.val sourceContext
          (sourceNode source removed targetNodeId)
          (tail.map (sourceNode source removed)) sourceItems
          (by simpa using sourceCompiled)
      obtain ⟨targetHead, targetHeadCompiled, sourceHeadEquality⟩ :=
        compileNode_singleton_reflect source removed targetWellFormed
          removedEndpoints targetContext sourceContext correspond
          sourceNodup targetNodeId sourceHeadCompiled
      obtain ⟨targetTail, targetTailCompiled, sourceTailEquality⟩ :=
        induction sourceTailCompiled
      simp only [ConcreteElaboration.compileNodes?] at targetHeadCompiled
      obtain ⟨targetItem, targetItemCompiled, targetHeadResult⟩ :=
        Option.bind_eq_some_iff.mp targetHeadCompiled
      have targetHeadEquality :
          (ItemSeq.cons targetItem .nil :
            ItemSeq definitions targetContext.sigs) =
            targetHead :=
        Option.some.inj targetHeadResult
      subst targetHead
      refine ⟨.cons targetItem targetTail, ?_, ?_⟩
      · simp only [ConcreteElaboration.compileNodes?]
        rw [targetItemCompiled, targetTailCompiled]
        rfl
      · cases sourceHeadEquality
        simp [sourceItemsEquality, sourceTailEquality,
          ItemSeq.renameWires]

/-- Reflect the exact stored node order at one copied region. -/
theorem compileRegionNodes_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (region : source.val.RegionId)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          (source.val.nodesAt region) =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      ConcreteElaboration.compileNodes? definitions
          (Target source removed) targetContext
          ((Target source removed).nodesAt
            (targetRegion source removed region)) =
        some targetItems ∧
      sourceItems =
        targetItems.renameWires
          (contextEmbedding source removed targetContext sourceContext
            correspond) := by
  apply compileNodes_reflect source removed targetWellFormed
    removedEndpoints targetContext sourceContext correspond sourceNodup
  rw [nodesAt_sources]
  exact sourceCompiled

private theorem climb_add
    (diagram : ConcreteDiagram definitionCount)
    (first second : Nat)
    (region : diagram.RegionId) :
    diagram.climb (first + second) region =
      (diagram.climb first region).bind (diagram.climb second) := by
  induction first generalizing region with
  | zero => simp
  | succ first induction =>
      cases regionData : diagram.regions region with
      | sheet =>
          simp [Nat.succ_add, ConcreteDiagram.climb, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, regionData, Nat.succ_add] using
            induction parent

private theorem climb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) :
    diagram.climb (steps + 1) diagram.root = none := by
  have rootData : diagram.regions diagram.root = .sheet :=
    wellFormed.root_is_sheet
  simp [ConcreteDiagram.climb, rootData]

private theorem climb_to_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          rw [climb_succ_root_none definitions diagram wellFormed right]
            at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          rw [climb_succ_root_none definitions diagram wellFormed left]
            at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet =>
              simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              apply congrArg Nat.succ
              apply induction
              · simpa [ConcreteDiagram.climb, regionData] using leftClimb
              · simpa [ConcreteDiagram.climb, regionData] using rightClimb

private theorem checked_reaches_root
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    ∃ steps : Fin (source.val.regionCount + 1),
      source.val.climb steps region = some source.val.root := by
  have checked :=
    (List.all_eq_true.mp source.property.all_regions_reach_root)
      region (Data.Finite.mem_allFin region)
  exact
    (ConcreteElaboration.encloses_iff_exists
      source.val source.val.root region).mp (of_decide_eq_true checked)

theorem checked_encloses_trans
    (source : CheckedDiagram definitions)
    {outer middle inner : source.val.RegionId}
    (outerMiddle : source.val.Encloses outer middle)
    (middleInner : source.val.Encloses middle inner) :
    source.val.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val outer middle).mp outerMiddle
  obtain ⟨middleSteps, middleClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val middle inner).mp middleInner
  obtain ⟨rootSteps, outerRoot⟩ := checked_reaches_root source outer
  have composed :
      source.val.climb (middleSteps.val + outerSteps.val) inner =
        some outer := by
    rw [climb_add source.val middleSteps.val outerSteps.val inner,
      middleClimb]
    exact outerClimb
  have composedRoot :
      source.val.climb
          ((middleSteps.val + outerSteps.val) + rootSteps.val) inner =
        some source.val.root := by
    rw [climb_add source.val
      (middleSteps.val + outerSteps.val) rootSteps.val inner, composed]
    exact outerRoot
  obtain ⟨canonicalRootSteps, canonicalRoot⟩ :=
    checked_reaches_root source inner
  have sameDepth :=
    climb_to_root_unique definitions source.val source.property
      composedRoot canonicalRoot
  have composedBound :
      middleSteps.val + outerSteps.val < source.val.regionCount + 1 := by
    omega
  exact
    (ConcreteElaboration.encloses_iff_exists source.val outer inner).mpr
      ⟨⟨middleSteps.val + outerSteps.val, composedBound⟩, composed⟩

private theorem child_outside
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region child : source.val.RegionId)
    (outside :
      ¬source.val.Encloses region (source.val.wires removed).scope)
    (member : child ∈ source.val.childrenOf region) :
    ¬source.val.Encloses child (source.val.wires removed).scope := by
  intro childSite
  have childData :=
    ConcreteElaboration.mem_childrenOf source.val region child member
  have parentChild :
      source.val.Encloses region child := by
    apply
      (ConcreteElaboration.encloses_iff_exists source.val region child).mpr
    refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
    simp [ConcreteDiagram.climb, childData]
  exact outside (checked_encloses_trans source parentChild childSite)

/-- Complete retained region binders preserve the reflected core equivalence. -/
private theorem finishRetainedRegion_equiv
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    (region : source.val.RegionId)
    (outside :
      ¬source.val.Encloses region (source.val.wires removed).scope)
    (above :
      ConcreteElaboration.ContextAbove source.val sourceContext region)
    (targetBody :
      Region definitions
        (targetContext.extend
          (targetRegion source removed region)).sigs)
    (sourceBody :
      Region definitions (sourceContext.extend region).sigs)
    (coreEquiv :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (targetEnv :
          Env pre
            (targetContext.extend
              (targetRegion source removed region)).sigs),
        denoteRegion pre definitionEnv targetEnv targetBody ↔
          denoteRegion pre definitionEnv
            (Env.comp targetEnv
              (contextProjection source removed
                (targetContext.extend
                  (targetRegion source removed region))
                (sourceContext.extend region)
                (extend_contexts_correspond source removed correspond region)
                (removed_absent_extend source removed sourceContext region
                  removedAbsent
                  (fun same => outside
                    (same ▸ source.val.encloses_refl region)))))
            sourceBody)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (targetOuter : Env pre targetContext.sigs) :
    denoteRegion pre definitionEnv targetOuter
        (ConcreteElaboration.finishRegion (Target source removed)
          targetContext (targetRegion source removed region) targetBody) ↔
      denoteRegion pre definitionEnv
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        (ConcreteElaboration.finishRegion source.val sourceContext region
          sourceBody) := by
  have notScope :
      region ≠ (source.val.wires removed).scope :=
    fun same => outside (same ▸ source.val.encloses_refl region)
  have sourceExtendedNodup :
      (sourceContext.extend region).ids.Nodup :=
    ConcreteElaboration.extend_nodup definitions source.val source.property
      sourceContext region above
  constructor
  · intro targetFinished
    obtain ⟨targetValues, targetCore⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions
        (Target source removed) targetContext
        (targetRegion source removed region) pre definitionEnv targetOuter
        targetBody).mp targetFinished
    obtain ⟨sourceValues, environments⟩ :=
      (extendedEnvironment_correspondence source removed targetContext
        sourceContext correspond region sourceExtendedNodup removedAbsent
        notScope pre
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        targetOuter rfl).2 targetValues
    apply
      (ConcreteElaboration.denote_finishRegion definitions source.val
        sourceContext region pre definitionEnv
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        sourceBody).mpr
    refine ⟨sourceValues, ?_⟩
    rw [environments]
    exact (coreEquiv pre definitionEnv _).mp targetCore
  · intro sourceFinished
    obtain ⟨sourceValues, sourceCore⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions source.val
        sourceContext region pre definitionEnv
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        sourceBody).mp sourceFinished
    obtain ⟨targetValues, environments⟩ :=
      (extendedEnvironment_correspondence source removed targetContext
        sourceContext correspond region sourceExtendedNodup removedAbsent
        notScope pre
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        targetOuter rfl).1 sourceValues
    apply
      (ConcreteElaboration.denote_finishRegion definitions
        (Target source removed) targetContext
        (targetRegion source removed region) pre definitionEnv targetOuter
        targetBody).mpr
    refine ⟨targetValues, ?_⟩
    apply (coreEquiv pre definitionEnv _).mpr
    rw [← environments]
    exact sourceCore

theorem compileChildren_reflect_of
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
        Option (Region definitions context.sigs))
    (targetRecurse : (region : (Target source removed).RegionId) →
      (context :
        ConcreteElaboration.WireContext (Target source removed)) →
        Option (Region definitions context.sigs))
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext) :
    ∀ (targetChildren : List (Target source removed).RegionId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext
          (targetChildren.map (sourceRegion source removed)) =
        some sourceItems →
      (∀ targetChild, targetChild ∈ targetChildren →
        ∀ sourceBody,
          sourceRecurse (sourceRegion source removed targetChild)
              sourceContext =
            some sourceBody →
          ∃ targetBody,
            targetRecurse targetChild targetContext =
                some targetBody ∧
              ∀ (removedAbsent : removed ∉ sourceContext.ids)
                (_outside :
                  ¬source.val.Encloses
                    (sourceRegion source removed targetChild)
                    (source.val.wires removed).scope),
              ∀ (pre : PreModel.{u})
                (definitionEnv : DefinitionEnv pre definitions)
                (targetEnv : Env pre targetContext.sigs),
                denoteRegion pre definitionEnv targetEnv targetBody ↔
                  denoteRegion pre definitionEnv
                    (Env.comp targetEnv
                      (contextProjection source removed targetContext
                        sourceContext correspond removedAbsent))
                    sourceBody) →
      ∃ targetItems : ItemSeq definitions targetContext.sigs,
        ConcreteElaboration.compileChildrenWith? definitions
            (Target source removed) targetRecurse targetContext
            targetChildren =
            some targetItems ∧
          ∀ (removedAbsent : removed ∉ sourceContext.ids)
            (_eachOutside :
              ∀ targetChild, targetChild ∈ targetChildren →
                ¬source.val.Encloses
                  (sourceRegion source removed targetChild)
                  (source.val.wires removed).scope),
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (targetEnv : Env pre targetContext.sigs),
            denoteItemSeq pre definitionEnv targetEnv targetItems ↔
              denoteItemSeq pre definitionEnv
                (Env.comp targetEnv
                  (contextProjection source removed targetContext
                    sourceContext correspond removedAbsent))
                sourceItems := by
  intro targetChildren
  induction targetChildren with
  | nil =>
      intro sourceItems sourceCompiled each
      have sourceEmpty : sourceItems = .nil := by
        simpa [ConcreteElaboration.compileChildrenWith?] using
          Option.some.inj sourceCompiled.symm
      subst sourceItems
      exact ⟨.nil, by
        simp [ConcreteElaboration.compileChildrenWith?], by simp⟩
  | cons targetChild tail induction =>
      intro sourceItems sourceCompiled each
      obtain ⟨sourceBody, sourceRest, sourceBodyCompiled,
          sourceRestCompiled, sourceExact⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions source.val sourceRecurse sourceContext
          (sourceRegion source removed targetChild)
          (tail.map (sourceRegion source removed)) sourceItems
          (by simpa using sourceCompiled)
      subst sourceItems
      obtain ⟨targetBody, targetBodyCompiled, bodyLaw⟩ :=
        each targetChild (by simp) sourceBody sourceBodyCompiled
      obtain ⟨targetRest, targetRestCompiled, restLaw⟩ :=
        induction sourceRestCompiled (by
          intro candidate member body compiled
          exact each candidate (List.mem_cons_of_mem targetChild member)
            body compiled)
      refine ⟨.cons (.cut targetBody) targetRest, ?_, ?_⟩
      · simp [ConcreteElaboration.compileChildrenWith?,
          targetBodyCompiled, targetRestCompiled]
      · intro removedAbsent eachOutside pre definitionEnv targetEnv
        simp only [denoteItemSeq_cons, cut_denotes_negation]
        exact and_congr
          (not_congr
            (bodyLaw removedAbsent
              (eachOutside targetChild (by simp))
              pre definitionEnv targetEnv))
          (restLaw removedAbsent
            (fun candidate member =>
              eachOutside candidate
                (List.mem_cons_of_mem targetChild member))
            pre definitionEnv targetEnv)

/--
Reflect one accepted fueled source-region compilation through singleton-wire
deletion. This theorem owns the only ordinary recursive traversal used by the
frame reflector.
-/
theorem compileRegion_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = []) :
    ∀ (fuel : Nat)
      (targetContext :
        ConcreteElaboration.WireContext (Target source removed))
      (sourceContext : ConcreteElaboration.WireContext source.val)
      (_correspond : ContextsCorrespond source removed
        targetContext sourceContext)
      (region : source.val.RegionId)
      (_above :
        ConcreteElaboration.ContextAbove source.val sourceContext region)
      {sourceBody : Region definitions sourceContext.sigs},
      ConcreteElaboration.compileRegion? definitions source.val fuel
          region sourceContext =
        some sourceBody →
      ∃ targetBody : Region definitions targetContext.sigs,
        ConcreteElaboration.compileRegion? definitions
            (Target source removed) fuel
            (targetRegion source removed region) targetContext =
            some targetBody ∧
          ∀ (removedAbsent : removed ∉ sourceContext.ids)
            (_outside :
              ¬source.val.Encloses region
                (source.val.wires removed).scope)
            (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (targetEnv : Env pre targetContext.sigs),
            denoteRegion pre definitionEnv targetEnv targetBody ↔
              denoteRegion pre definitionEnv
                (Env.comp targetEnv
                  (contextProjection source removed targetContext
                    sourceContext _correspond removedAbsent))
                sourceBody := by
  intro fuel
  induction fuel with
  | zero =>
      intro targetContext sourceContext correspond region above sourceBody
        sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel induction =>
      intro targetContext sourceContext correspond region above sourceBody
        sourceCompiled
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled
      cases sourceNodesEquation :
          ConcreteElaboration.compileNodes? definitions source.val
            (sourceContext.extend region) (source.val.nodesAt region) with
      | none =>
          rw [sourceNodesEquation] at sourceCompiled
          simp at sourceCompiled
      | some sourceNodes =>
          rw [sourceNodesEquation] at sourceCompiled
          cases sourceChildrenEquation :
              ConcreteElaboration.compileChildrenWith? definitions source.val
                (ConcreteElaboration.compileRegion? definitions source.val
                  fuel)
                (sourceContext.extend region)
                (source.val.childrenOf region) with
          | none =>
              rw [sourceChildrenEquation] at sourceCompiled
              simp at sourceCompiled
          | some sourceChildren =>
              rw [sourceChildrenEquation] at sourceCompiled
              have sourceBodyExact :
                  ConcreteElaboration.finishRegion source.val sourceContext
                      region
                      (.mk (sourceNodes.append sourceChildren)) =
                    sourceBody :=
                Option.some.inj sourceCompiled
              subst sourceBody
              have sourceExtendedNodup :
                  (sourceContext.extend region).ids.Nodup :=
                ConcreteElaboration.extend_nodup definitions source.val
                  source.property sourceContext region above
              let targetExtended :=
                targetContext.extend (targetRegion source removed region)
              let sourceExtended := sourceContext.extend region
              have extendedCorrespond :
                  ContextsCorrespond source removed
                    targetExtended sourceExtended := by
                exact extend_contexts_correspond source removed correspond
                  region
              obtain ⟨targetNodes, targetNodesCompiled, sourceNodesExact⟩ :=
                compileRegionNodes_reflect source removed targetWellFormed
                  removedEndpoints targetExtended sourceExtended
                  extendedCorrespond sourceExtendedNodup region
                  sourceNodesEquation
              have sourceChildrenMapped :
                  ConcreteElaboration.compileChildrenWith? definitions
                      source.val
                      (ConcreteElaboration.compileRegion? definitions
                        source.val fuel)
                      sourceExtended
                      (((Target source removed).childrenOf
                        (targetRegion source removed region)).map
                        (sourceRegion source removed)) =
                    some sourceChildren := by
                rw [childrenOf_sources]
                exact sourceChildrenEquation
              obtain ⟨targetChildren, targetChildrenCompiled,
                  targetChildrenLaw⟩ :=
                compileChildren_reflect_of source removed targetExtended
                  sourceExtended
                  (ConcreteElaboration.compileRegion? definitions
                    source.val fuel)
                  (ConcreteElaboration.compileRegion? definitions
                    (Target source removed) fuel)
                  extendedCorrespond
                  ((Target source removed).childrenOf
                    (targetRegion source removed region))
                  sourceChildrenMapped (by
                    intro targetChild targetMember childBody childCompiled
                    have sourceMember :
                        sourceRegion source removed targetChild ∈
                          source.val.childrenOf region := by
                      rw [← childrenOf_sources source removed region]
                      exact List.mem_map.mpr
                        ⟨targetChild, targetMember, rfl⟩
                    have childData :=
                      ConcreteElaboration.mem_childrenOf source.val region
                        (sourceRegion source removed targetChild)
                        sourceMember
                    obtain ⟨targetBody, targetCompiled, targetLaw⟩ :=
                      induction targetExtended sourceExtended
                        extendedCorrespond
                        (sourceRegion source removed targetChild)
                        (ConcreteElaboration.extend_above_child definitions
                          source.val source.property sourceContext region
                          (sourceRegion source removed targetChild) above
                          childData)
                        childCompiled
                    refine ⟨targetBody, ?_, ?_⟩
                    · simpa only [targetRegion_sourceRegion] using
                        targetCompiled
                    · exact targetLaw)
              refine
                ⟨ConcreteElaboration.finishRegion
                    (Target source removed) targetContext
                    (targetRegion source removed region)
                    (.mk (targetNodes.append targetChildren)), ?_, ?_⟩
              · simp only [ConcreteElaboration.compileRegion?]
                rw [targetNodesCompiled, targetChildrenCompiled]
                rfl
              · intro removedAbsent outside pre definitionEnv targetEnv
                apply finishRetainedRegion_equiv source removed targetContext
                  sourceContext correspond removedAbsent region outside above
                intro currentPre currentDefinitions currentTarget
                simp only [denoteRegion, denoteItemSeq_append]
                have nodeLaw :
                    denoteItemSeq currentPre currentDefinitions currentTarget
                          targetNodes ↔
                      denoteItemSeq currentPre currentDefinitions
                        (Env.comp currentTarget
                          (contextProjection source removed targetExtended
                            sourceExtended extendedCorrespond
                            (removed_absent_extend source removed sourceContext
                              region removedAbsent
                              (fun same => outside
                                (same ▸ source.val.encloses_refl region)))))
                        sourceNodes := by
                  rw [sourceNodesExact, denoteItemSeq_renameWires,
                    contextProjection_embedding_environment source removed
                      targetExtended sourceExtended extendedCorrespond
                      sourceExtendedNodup
                      (removed_absent_extend source removed sourceContext
                        region removedAbsent
                        (fun same => outside
                          (same ▸ source.val.encloses_refl region)))
                      currentPre currentTarget]
                exact and_congr nodeLaw
                  (targetChildrenLaw
                    (removed_absent_extend source removed sourceContext region
                      removedAbsent
                      (fun same => outside
                        (same ▸ source.val.encloses_refl region)))
                    (fun targetChild targetMember =>
                      child_outside source removed region
                        (sourceRegion source removed targetChild) outside
                        (by
                          rw [← childrenOf_sources source removed region]
                          exact List.mem_map.mpr
                            ⟨targetChild, targetMember, rfl⟩))
                    currentPre currentDefinitions currentTarget)

/--
Reflect the unbound body owned by one copied region through the same fueled
ordinary traversal.
-/
theorem compileRegionBody_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (fuel : Nat)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (above :
      ConcreteElaboration.ContextAbove source.val sourceContext region)
    {sourceBody :
      Region definitions (sourceContext.extend region).sigs}
    (sourceCompiled :
      compileRegionBody? definitions source.val fuel region sourceContext =
        some sourceBody) :
    ∃ targetBody :
        Region definitions
          (targetContext.extend
            (targetRegion source removed region)).sigs,
      compileRegionBody? definitions (Target source removed) fuel
          (targetRegion source removed region) targetContext =
        some targetBody := by
  cases sourceNodesEquation :
      ConcreteElaboration.compileNodes? definitions source.val
        (sourceContext.extend region) (source.val.nodesAt region) with
  | none =>
      simp [compileRegionBody?, sourceNodesEquation] at sourceCompiled
  | some sourceNodes =>
      cases sourceChildrenEquation :
          ConcreteElaboration.compileChildrenWith? definitions source.val
            (ConcreteElaboration.compileRegion? definitions source.val fuel)
            (sourceContext.extend region) (source.val.childrenOf region) with
      | none =>
          simp [compileRegionBody?, sourceNodesEquation,
            sourceChildrenEquation] at sourceCompiled
      | some sourceChildren =>
          have sourceFull :
              ConcreteElaboration.compileRegion? definitions source.val
                  (fuel + 1) region sourceContext =
                some
                  (ConcreteElaboration.finishRegion source.val sourceContext
                    region (.mk (sourceNodes.append sourceChildren))) := by
            simp [ConcreteElaboration.compileRegion?,
              sourceNodesEquation, sourceChildrenEquation]
          obtain ⟨targetFull, targetCompiled, _targetLaw⟩ :=
            compileRegion_reflect.{0} source removed targetWellFormed
              removedEndpoints (fuel + 1) targetContext sourceContext
              correspond region above sourceFull
          simp only [ConcreteElaboration.compileRegion?] at targetCompiled
          cases targetNodesEquation :
              ConcreteElaboration.compileNodes? definitions
                (Target source removed)
                (targetContext.extend
                  (targetRegion source removed region))
                ((Target source removed).nodesAt
                  (targetRegion source removed region)) with
          | none =>
              rw [targetNodesEquation] at targetCompiled
              simp at targetCompiled
          | some targetNodes =>
              rw [targetNodesEquation] at targetCompiled
              cases targetChildrenEquation :
                  ConcreteElaboration.compileChildrenWith? definitions
                    (Target source removed)
                    (ConcreteElaboration.compileRegion? definitions
                      (Target source removed) fuel)
                    (targetContext.extend
                      (targetRegion source removed region))
                    ((Target source removed).childrenOf
                      (targetRegion source removed region)) with
              | none =>
                  rw [targetChildrenEquation] at targetCompiled
                  simp at targetCompiled
              | some targetChildren =>
                  refine
                    ⟨.mk (targetNodes.append targetChildren), ?_⟩
                  simp [compileRegionBody?, targetNodesEquation,
                    targetChildrenEquation]

/--
Insert one caller-supplied value at every occurrence of a removed wire in an
ordered source wire list. The compiler supplies nodup local lists, so the
result-indexed use inserts exactly once.
-/
private def castWireValues
    {pre : PreModel.{u}} {source target : List Sig}
    (exact : source = target)
    (values : ConcreteElaboration.WireValues pre source) :
    ConcreteElaboration.WireValues pre target :=
  exact ▸ values

def insertRemovedValue
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (specified : pre.Domain (source.val.wires removed).sig) :
    (wires : List source.val.WireId) →
      ConcreteElaboration.WireValues pre
        ((wires.filter fun wire => decide (wire ≠ removed)).map
          (fun wire => (source.val.wires wire).sig)) →
      ConcreteElaboration.WireValues pre
        (wires.map fun wire => (source.val.wires wire).sig)
  | [], values =>
      castWireValues (by simp) values
  | head :: tail, values => by
      by_cases same : head = removed
      · exact
          castWireValues (by simp [same]) <|
            .cons (same ▸ specified)
              (insertRemovedValue source removed specified tail
                (castWireValues (by simp [same]) values))
      · let retained :
            ConcreteElaboration.WireValues pre
              ((source.val.wires head).sig ::
                ((tail.filter fun wire =>
                    decide (wire ≠ removed)).map
                  fun wire => (source.val.wires wire).sig)) :=
            castWireValues (by simp [same]) values
        exact
          match retained with
          | .cons value rest =>
              .cons value
                (insertRemovedValue source removed specified tail rest)

private theorem extendEnvironmentFor_insertRemovedValue_of_origin
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (specified : pre.Domain (source.val.wires removed).sig)
    (outerIds wires : List source.val.WireId)
    (allNodup : (wires ++ outerIds).Nodup)
    (removedOuterAbsent : removed ∉ outerIds)
    (values :
      ConcreteElaboration.WireValues pre
        ((wires.filter fun wire => decide (wire ≠ removed)).map
          fun wire => (source.val.wires wire).sig))
    (outerEnv :
      Env pre (outerIds.map fun wire => (source.val.wires wire).sig))
    {sig : Sig}
    (value :
      Var
        ((wires ++ outerIds).map
          fun wire => (source.val.wires wire).sig)
        sig)
    (origin :
      ConcreteElaboration.WireContext.origin source.val
          (wires ++ outerIds) value =
        removed)
    (signature : (source.val.wires removed).sig = sig) :
    ConcreteElaboration.extendEnvironmentFor source.val outerIds wires
        (insertRemovedValue source removed specified wires values)
        outerEnv sig value =
      congrArg pre.Domain signature ▸ specified := by
  induction wires with
  | nil =>
      have member :=
        InsertionCompilation.NaturalityInternal.origin_member source.val
          outerIds value
      exact (removedOuterAbsent (origin ▸ member)).elim
  | cons head tail induction =>
      rw [List.cons_append, List.nodup_cons] at allNodup
      by_cases same : head = removed
      · subst head
        cases value with
        | here =>
            simp only [ConcreteElaboration.extendEnvironmentFor,
              insertRemovedValue]
            rfl
        | there rest =>
            have tailOrigin :
                ConcreteElaboration.WireContext.origin source.val
                    (tail ++ outerIds) rest =
                  removed := origin
            have member :=
              InsertionCompilation.NaturalityInternal.origin_member
                source.val (tail ++ outerIds) rest
            exact (allNodup.1 (tailOrigin ▸ member)).elim
      · cases value with
        | here =>
            exact (same origin).elim
        | there tailValue =>
            let retainedValues :
                ConcreteElaboration.WireValues pre
                  ((source.val.wires head).sig ::
                    ((tail.filter fun wire =>
                        decide (wire ≠ removed)).map
                      fun wire => (source.val.wires wire).sig)) :=
              castWireValues (by simp [same]) values
            have insertedExact :
                insertRemovedValue source removed specified
                    (head :: tail) values =
                  match retainedValues with
                  | .cons retained rest =>
                      ConcreteElaboration.WireValues.cons retained
                        (insertRemovedValue source removed specified
                          tail rest) := by
              simp only [insertRemovedValue, same, ↓reduceDIte]
              rfl
            rw [insertedExact]
            cases retainedValues with
            | cons _ rest =>
                simp only [ConcreteElaboration.extendEnvironmentFor,
                  Env.extend_there]
                exact induction allNodup.2 rest tailValue origin

/--
The completed source-scope environment assigns the caller's inserted value to
the unique visible variable whose concrete origin is the removed wire.
-/
theorem extendEnvironment_insertRemovedValue_of_origin
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (sourceContext :
      ConcreteElaboration.WireContext source.val)
    (removedContextAbsent : removed ∉ sourceContext.ids)
    (visibleNodup :
      (sourceContext.extend (source.val.wires removed).scope).ids.Nodup)
    (specified : pre.Domain (source.val.wires removed).sig)
    (values :
      ConcreteElaboration.WireValues pre
        (((source.val.wiresAt
            (source.val.wires removed).scope).filter
          fun wire => decide (wire ≠ removed)).map
            fun wire => (source.val.wires wire).sig))
    (outerEnv : Env pre sourceContext.sigs)
    (value :
      Var
        (sourceContext.extend
          (source.val.wires removed).scope).sigs
        (source.val.wires removed).sig)
    (origin :
      ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend
            (source.val.wires removed).scope).ids value =
        removed) :
    ConcreteElaboration.extendEnvironment source.val sourceContext
        (source.val.wires removed).scope
        (insertRemovedValue source removed specified
          (source.val.wiresAt (source.val.wires removed).scope) values)
        outerEnv (source.val.wires removed).sig value =
      specified := by
  exact
    extendEnvironmentFor_insertRemovedValue_of_origin source removed
      specified sourceContext.ids
      (source.val.wiresAt (source.val.wires removed).scope)
      visibleNodup removedContextAbsent values outerEnv value origin rfl

private theorem
    extendEnvironmentFor_insertRemovedValue_irrelevant_of_origin_ne
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (first second : pre.Domain (source.val.wires removed).sig)
    (outerIds wires : List source.val.WireId)
    (values :
      ConcreteElaboration.WireValues pre
        ((wires.filter fun wire => decide (wire ≠ removed)).map
          fun wire => (source.val.wires wire).sig))
    (outerEnv :
      Env pre (outerIds.map fun wire => (source.val.wires wire).sig))
    {sig : Sig}
    (value :
      Var
        ((wires ++ outerIds).map
          fun wire => (source.val.wires wire).sig)
        sig)
    (survives :
      ConcreteElaboration.WireContext.origin source.val
          (wires ++ outerIds) value ≠
        removed) :
    ConcreteElaboration.extendEnvironmentFor source.val outerIds wires
        (insertRemovedValue source removed first wires values)
        outerEnv sig value =
      ConcreteElaboration.extendEnvironmentFor source.val outerIds wires
        (insertRemovedValue source removed second wires values)
        outerEnv sig value := by
  induction wires with
  | nil => rfl
  | cons head tail induction =>
      by_cases same : head = removed
      · subst head
        cases value with
        | here =>
            exact (survives rfl).elim
        | there tailValue =>
            simp only [ConcreteElaboration.extendEnvironmentFor,
              insertRemovedValue, Env.extend_there]
            exact
              induction (castWireValues (by simp) values)
                tailValue survives
      · cases value with
        | here =>
            let retainedValues :
                ConcreteElaboration.WireValues pre
                  ((source.val.wires head).sig ::
                    ((tail.filter fun wire =>
                        decide (wire ≠ removed)).map
                      fun wire => (source.val.wires wire).sig)) :=
              castWireValues (by simp [same]) values
            cases retainedEquation : retainedValues with
            | cons retained rest =>
                have firstExact :
                    insertRemovedValue source removed first
                        (head :: tail) values =
                      .cons retained
                        (insertRemovedValue source removed first
                          tail rest) := by
                  simp only [insertRemovedValue, same, ↓reduceDIte]
                  change
                    (match retainedValues with
                    | .cons value tailValues =>
                        ConcreteElaboration.WireValues.cons value
                          (insertRemovedValue source removed first
                            tail tailValues)) =
                      _
                  simpa only [retainedEquation]
                have secondExact :
                    insertRemovedValue source removed second
                        (head :: tail) values =
                      ConcreteElaboration.WireValues.cons retained
                        (insertRemovedValue source removed second
                          tail rest) := by
                  simp only [insertRemovedValue, same, ↓reduceDIte]
                  change
                    (match retainedValues with
                    | .cons value tailValues =>
                        ConcreteElaboration.WireValues.cons value
                          (insertRemovedValue source removed second
                            tail tailValues)) =
                      _
                  simpa only [retainedEquation]
                rw [firstExact, secondExact]
                rfl
        | there tailValue =>
            let retainedValues :
                ConcreteElaboration.WireValues pre
                  ((source.val.wires head).sig ::
                    ((tail.filter fun wire =>
                        decide (wire ≠ removed)).map
                      fun wire => (source.val.wires wire).sig)) :=
              castWireValues (by simp [same]) values
            cases retainedEquation : retainedValues with
            | cons retained rest =>
                have firstExact :
                    insertRemovedValue source removed first
                        (head :: tail) values =
                      ConcreteElaboration.WireValues.cons retained
                        (insertRemovedValue source removed first
                          tail rest) := by
                  simp only [insertRemovedValue, same, ↓reduceDIte]
                  change
                    (match retainedValues with
                    | .cons value tailValues =>
                        ConcreteElaboration.WireValues.cons value
                          (insertRemovedValue source removed first
                            tail tailValues)) =
                      _
                  simpa only [retainedEquation]
                have secondExact :
                    insertRemovedValue source removed second
                        (head :: tail) values =
                      ConcreteElaboration.WireValues.cons retained
                        (insertRemovedValue source removed second
                          tail rest) := by
                  simp only [insertRemovedValue, same, ↓reduceDIte]
                  change
                    (match retainedValues with
                    | .cons value tailValues =>
                        ConcreteElaboration.WireValues.cons value
                          (insertRemovedValue source removed second
                            tail tailValues)) =
                      _
                  simpa only [retainedEquation]
                rw [firstExact, secondExact]
                simp only [ConcreteElaboration.extendEnvironmentFor,
                  Env.extend_there]
                exact induction rest tailValue survives

/--
Changing the value inserted for the removed wire leaves every surviving
visible variable unchanged.
-/
theorem extendEnvironment_insertRemovedValue_irrelevant_of_origin_ne
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (sourceContext :
      ConcreteElaboration.WireContext source.val)
    (first second : pre.Domain (source.val.wires removed).sig)
    (values :
      ConcreteElaboration.WireValues pre
        (((source.val.wiresAt
            (source.val.wires removed).scope).filter
          fun wire => decide (wire ≠ removed)).map
            fun wire => (source.val.wires wire).sig))
    (outerEnv : Env pre sourceContext.sigs)
    {sig : Sig}
    (value :
      Var
        (sourceContext.extend
          (source.val.wires removed).scope).sigs
        sig)
    (survives :
      ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend
            (source.val.wires removed).scope).ids value ≠
        removed) :
    ConcreteElaboration.extendEnvironment source.val sourceContext
        (source.val.wires removed).scope
        (insertRemovedValue source removed first
          (source.val.wiresAt (source.val.wires removed).scope) values)
        outerEnv sig value =
      ConcreteElaboration.extendEnvironment source.val sourceContext
        (source.val.wires removed).scope
        (insertRemovedValue source removed second
          (source.val.wiresAt (source.val.wires removed).scope) values)
        outerEnv sig value := by
  exact
    extendEnvironmentFor_insertRemovedValue_irrelevant_of_origin_ne
      source removed first second sourceContext.ids
      (source.val.wiresAt (source.val.wires removed).scope)
      values outerEnv value survives

/--
Lift a site-body implication across the whole completed dying-wire scope.
The plain target supplies values for all surviving local wires; the caller's
specified dying value is inserted at its exact original source-list position.
Relating the two outer environments and proving the body implication belong to
the separate enclosing-context composition layer.
-/
theorem finishDyingRegion_implication
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetOuterEnv : Env pre targetContext.sigs)
    (sourceOuterEnv : Env pre sourceContext.sigs)
    (specified :
      ∀ (retainedOuter : Env pre targetContext.sigs)
        (retainedLocal :
          ConcreteElaboration.WireValues pre
            (((Target source removed).wiresAt
              (targetRegion source removed
                (source.val.wires removed).scope)).map
              fun wire => ((Target source removed).wires wire).sig)),
        pre.Domain (source.val.wires removed).sig)
    (targetBody :
      Region definitions
        (targetContext.extend
          (targetRegion source removed
            (source.val.wires removed).scope)).sigs)
    (sourceBody :
      Region definitions
        (sourceContext.extend
          (source.val.wires removed).scope).sigs)
    (bodyImplication :
      ∀ targetValues :
          ConcreteElaboration.WireValues pre
            (((Target source removed).wiresAt
              (targetRegion source removed
                (source.val.wires removed).scope)).map
              fun wire => ((Target source removed).wires wire).sig),
        denoteRegion pre definitionEnv
            (ConcreteElaboration.extendEnvironment
              (Target source removed) targetContext
              (targetRegion source removed
                (source.val.wires removed).scope)
              targetValues targetOuterEnv)
            targetBody →
          denoteRegion pre definitionEnv
            (ConcreteElaboration.extendEnvironment source.val sourceContext
              (source.val.wires removed).scope
              (insertRemovedValue source removed
                (specified targetOuterEnv targetValues)
                (source.val.wiresAt (source.val.wires removed).scope)
                ((wiresAt_signatures source removed
                  (source.val.wires removed).scope) ▸ targetValues))
              sourceOuterEnv)
            sourceBody) :
    denoteRegion pre definitionEnv targetOuterEnv
        (ConcreteElaboration.finishRegion
          (Target source removed) targetContext
          (targetRegion source removed
            (source.val.wires removed).scope)
          targetBody) →
      denoteRegion pre definitionEnv sourceOuterEnv
        (ConcreteElaboration.finishRegion source.val sourceContext
          (source.val.wires removed).scope sourceBody) := by
  intro targetFinished
  obtain ⟨targetValues, targetCore⟩ :=
    (ConcreteElaboration.denote_finishRegion definitions
      (Target source removed) targetContext
      (targetRegion source removed
        (source.val.wires removed).scope)
      pre definitionEnv targetOuterEnv targetBody).mp targetFinished
  apply
    (ConcreteElaboration.denote_finishRegion definitions source.val
      sourceContext (source.val.wires removed).scope
      pre definitionEnv sourceOuterEnv sourceBody).mpr
  exact
    ⟨insertRemovedValue source removed
        (specified targetOuterEnv targetValues)
        (source.val.wiresAt (source.val.wires removed).scope)
        ((wiresAt_signatures source removed
          (source.val.wires removed).scope) ▸ targetValues),
      bodyImplication targetValues targetCore⟩

end ExhaustedWireRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
