import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawCore

namespace VisualProof

namespace ConcreteWireQuantifier


variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}

open VisualProof.Data.Finite

/-- Allocation-neutral region origins for an accepted construction prefix. -/
abbrev PrefixRegionOrigin
    (steps : List (RelationJoinStep source dying content)) :=
  source.val.RegionId ⊕
    Σ _occurrence : Fin steps.length,
      { region : content.val.diagram.RegionId //
        region ≠ content.val.diagram.root }

/-- Allocation-neutral broad node origins for an accepted construction prefix. -/
abbrev PrefixNodeOrigin
    (steps : List (RelationJoinStep source dying content)) :=
  source.val.NodeId ⊕
    Σ occurrence : Fin steps.length,
      content.val.diagram.NodeId ⊕
        Fin ((steps.get occurrence).attachment.identityRequests.length)

/-- A broad node origin is live when no accepted prefix step consumed it. -/
def PrefixNodeLive
    {steps : List (RelationJoinStep source dying content)} :
    PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps → Prop
  | .inl node => node ∉ steps.map RelationJoinStep.application
  | .inr _ => True

/-- Remove one dense position without searching an enumeration. -/
def dropFin
    {count : Nat}
    (removed target : Fin (count + 1))
    (different : target ≠ removed) : Fin count :=
  if before : target.val < removed.val then
    ⟨target.val, by omega⟩
  else
    ⟨target.val - 1, by
      have targetBound := target.isLt
      omega⟩

/-- Restore one dense position around a removed position. -/
def restoreFin
    {count : Nat}
    (removed : Fin (count + 1))
    (position : Fin count) : Fin (count + 1) :=
  if before : position.val < removed.val then
    ⟨position.val, by omega⟩
  else
    ⟨position.val + 1, by omega⟩

theorem restoreFin_ne
    {count : Nat}
    (removed : Fin (count + 1))
    (position : Fin count) :
    restoreFin removed position ≠ removed := by
  intro same
  have values := congrArg Fin.val same
  unfold restoreFin at values
  split at values <;> simp only [Fin.val_mk] at values <;> omega

@[simp] theorem restoreFin_dropFin
    {count : Nat}
    (removed target : Fin (count + 1))
    (different : target ≠ removed) :
    restoreFin removed (dropFin removed target different) = target := by
  apply Fin.ext
  have valuesDifferent : target.val ≠ removed.val := by
    intro same
    exact different (Fin.ext same)
  by_cases before : target.val < removed.val
  · simp [dropFin, restoreFin, before]
  · have after : ¬ target.val - 1 < removed.val := by omega
    simp [dropFin, restoreFin, before, after]
    omega

@[simp] theorem dropFin_restoreFin
    {count : Nat}
    (removed : Fin (count + 1))
    (position : Fin count) :
    dropFin removed (restoreFin removed position)
        (restoreFin_ne removed position) = position := by
  apply Fin.ext
  by_cases before : position.val < removed.val
  · simp [dropFin, restoreFin, before]
  · have after : ¬ position.val + 1 < removed.val := by omega
    simp [dropFin, restoreFin, before, after]

/-- Boundary equations for the constructive dense-position restoration map. -/
@[simp] theorem restoreFin_zero
    {count : Nat} (position : Fin count) :
    restoreFin (0 : Fin (count + 1)) position = Fin.succ position := by
  apply Fin.ext
  simp [restoreFin]

@[simp] theorem restoreFin_succ_zero
    {count : Nat} (removed : Fin (count + 1)) :
    restoreFin (Fin.succ removed) (0 : Fin (count + 1)) = 0 := by
  apply Fin.ext
  simp [restoreFin]

@[simp] theorem restoreFin_succ_succ
    {count : Nat} (removed : Fin (count + 1)) (position : Fin count) :
    restoreFin (Fin.succ removed) (Fin.succ position) =
      Fin.succ (restoreFin removed position) := by
  apply Fin.ext
  by_cases before : position.val < removed.val
  · simp [restoreFin, before]
  · simp [restoreFin, before]

theorem retained_allFin_eq_map_restoreFin
    (count : Nat) (removed : Fin (count + 1)) :
    (allFin (count + 1)).filter
        (fun value => decide (value ≠ removed)) =
      (allFin count).map (restoreFin removed) := by
  induction count with
  | zero =>
      have removedExact : removed = 0 := by apply Fin.ext; omega
      rw [removedExact]
      simp [allFin]
  | succ count induction =>
      refine Fin.cases ?_ (fun tail => ?_) removed
      · change
          List.filter (fun value => decide (value ≠ 0))
              (0 :: (allFin (count + 1)).map Fin.succ) =
            (allFin (count + 1)).map (restoreFin 0)
        rw [List.filter_cons]
        have headRejected :
            decide ((0 : Fin (count + 1 + 1)) ≠ 0) = false := by simp
        rw [headRejected]
        simp only [Bool.false_eq_true, if_false, List.filter_map]
        have predicateExact :
            ((fun value : Fin (count + 1 + 1) => decide (value ≠ 0)) ∘
                Fin.succ) =
              (fun _ : Fin (count + 1) => true) := by
          funext value
          change decide (Fin.succ value ≠ 0) = true
          apply decide_eq_true
          exact Fin.succ_ne_zero value
        rw [predicateExact]
        rw [List.filter_eq_self.mpr]
        · apply List.map_congr_left
          intro position _
          exact (restoreFin_zero position).symm
        · intro value _
          rfl
      · change
          List.filter (fun value => decide (value ≠ Fin.succ tail))
              (0 :: (allFin (count + 1)).map Fin.succ) =
            (0 :: (allFin count).map Fin.succ).map
              (restoreFin (Fin.succ tail))
        rw [List.filter_cons]
        have headRetained :
            decide ((0 : Fin (count + 1 + 1)) ≠ Fin.succ tail) = true := by
          apply decide_eq_true
          intro same
          exact Fin.succ_ne_zero tail same.symm
        rw [headRetained]
        simp only [if_true, List.filter_map]
        have predicateExact :
            ((fun value : Fin (count + 1 + 1) =>
                decide (value ≠ Fin.succ tail)) ∘ Fin.succ) =
              (fun value : Fin (count + 1) => decide (value ≠ tail)) := by
          funext value
          simp
        rw [predicateExact]
        rw [induction tail]
        simp only [List.map_cons, restoreFin_succ_zero, List.map_map]
        congr 1
        apply List.map_congr_left
        intro position _
        exact (restoreFin_succ_succ tail position).symm

/-- Lift a region origin through one accepted construction step. -/
def liftRegionOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps →
    PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])
  | .inl region => .inl region
  | .inr ⟨occurrence, region⟩ =>
      .inr ⟨Fin.cast (by simp) (Fin.castAdd 1 occurrence), region⟩

/-- Introduce a non-root copied-fragment region at the newest occurrence. -/
def freshRegionOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step]) :=
  .inr ⟨Fin.cast (by simp) (Fin.last steps.length), region⟩

theorem fragmentRegionCount :
    (content.val.diagram.regionsList.filter
          (fun region => decide (region ≠ content.val.diagram.root))).length + 1 =
      content.val.diagram.regionCount := by
  have exact := filter_ne_length_add_one_of_nodup_mem
    (values := content.val.diagram.regionsList)
    (by simpa [ConcreteDiagram.regionsList] using
      Data.Finite.allFin_nodup content.val.diagram.regionCount)
    content.val.diagram.root
    (by simp [ConcreteDiagram.regionsList, Data.Finite.mem_allFin])
  simpa [ConcreteDiagram.regionsList,
    Data.Finite.allFin_eq_finRange] using exact

def nonrootRegionPosition
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    Fin (content.val.diagram.regionsList.filter
      (fun current => decide (current ≠ content.val.diagram.root))).length :=
  let count := fragmentRegionCount (content := content)
  dropFin
    (Fin.cast count.symm content.val.diagram.root)
    (Fin.cast count.symm region.1)
    (by
      intro same
      apply region.2
      apply Fin.ext
      simpa using congrArg Fin.val same)

def nonrootRegionAt
    (position : Fin (content.val.diagram.regionsList.filter
      (fun current => decide (current ≠ content.val.diagram.root))).length) :
    { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root } :=
  let count := fragmentRegionCount (content := content)
  let removed := Fin.cast count.symm content.val.diagram.root
  ⟨Fin.cast count (restoreFin removed position), by
    intro same
    apply restoreFin_ne removed position
    apply Fin.ext
    simpa [removed] using congrArg Fin.val same⟩

@[simp] theorem nonrootRegionAt_position
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    nonrootRegionAt (nonrootRegionPosition region) = region := by
  apply Subtype.ext
  apply Fin.ext
  simp [nonrootRegionAt, nonrootRegionPosition]

@[simp] theorem nonrootRegionPosition_at
    (position : Fin (content.val.diagram.regionsList.filter
      (fun current => decide (current ≠ content.val.diagram.root))).length) :
    nonrootRegionPosition (nonrootRegionAt position) = position := by
  apply Fin.ext
  simp [nonrootRegionAt, nonrootRegionPosition]

theorem nonrootRegionAt_injective :
    Function.Injective (nonrootRegionAt (content := content)) := by
  intro left right same
  have positions := congrArg nonrootRegionPosition same
  simpa using positions

/-- Direct checked allocation for one fresh non-root region position. -/
def checkedFreshRegionAtPosition
    (step : RelationJoinStep source dying content)
    (position : Fin step.attachment.fragmentRegions.length) :
    step.checked.val.RegionId :=
  ⟨step.prior.val.regionCount + position.val, by
    have checkedCount := step.checked_regionCount
    omega⟩

/-- Direct checked target for one retained prior region. -/
def checkedRetainedRegion
    (step : RelationJoinStep source dying content)
    (target : step.prior.val.RegionId) : step.checked.val.RegionId :=
  ⟨target.val, by
    have checkedCount := step.checked_regionCount
    have targetBound := target.isLt
    omega⟩

theorem checkedFreshRegionAtPosition_eq_checkedFragmentRegion
    (step : RelationJoinStep source dying content)
    (position : Fin step.attachment.fragmentRegions.length) :
    checkedFreshRegionAtPosition step position =
      step.checkedFragmentRegion
        (step.attachment.fragmentRegions.get position) := by
  apply Fin.ext
  have baseCount := step.base_regionCount
  have nonroot : step.attachment.fragmentRegions.get position ≠
      content.val.diagram.root := by
    have member := List.get_mem step.attachment.fragmentRegions position
    change step.attachment.fragmentRegions.get position ∈
      content.val.diagram.regionsList.filter
        (fun region => decide (region ≠ content.val.diagram.root)) at member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have nodup : step.attachment.fragmentRegions.Nodup := by
    unfold ConcreteSpliceAttachment.fragmentRegions
    simpa [ConcreteDiagram.regionsList] using
      (Data.Finite.allFin_nodup content.val.diagram.regionCount).filter
        (fun region => decide (region ≠ content.val.diagram.root))
  have indexExact := DenseList.index_get
    step.attachment.fragmentRegions nodup position
  have fragmentExact :
      step.attachment.fragmentRegion
          (step.attachment.fragmentRegions.get position) =
        step.attachment.freshRegion position := by
    unfold ConcreteSpliceAttachment.fragmentRegion
    rw [dif_neg nonroot]
    exact congrArg step.attachment.freshRegion indexExact
  simp only [checkedFreshRegionAtPosition,
    RelationJoinStep.checkedFragmentRegion, Fin.val_cast]
  rw [fragmentExact]
  simp [ConcreteSpliceAttachment.freshRegion, baseCount]

theorem checkedRetainedRegion_eq_checkedPriorRegion
    (step : RelationJoinStep source dying content)
    (target : step.prior.val.RegionId) :
    checkedRetainedRegion step target = step.checkedPriorRegion target := by
  apply Fin.ext
  simp [checkedRetainedRegion]

/-- Constructive carrier counts owned by the raw step constructor. -/
structure AtlasStepCounts
    (step : RelationJoinStep source dying content) : Type where
  baseNodeCountAddOne :
    step.base.val.nodeCount + 1 = step.prior.val.nodeCount
  checkedNodeCountAddOne :
    step.checked.val.nodeCount + 1 =
      step.prior.val.nodeCount + content.val.diagram.nodeCount +
        step.attachment.identityRequests.length

def priorNodePosition
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (target : step.prior.val.NodeId)
    (different : target ≠ step.priorApplication) :
    step.base.val.NodeId :=
  let count := counts.baseNodeCountAddOne
  dropFin
    (Fin.cast count.symm step.priorApplication)
    (Fin.cast count.symm target)
    (by
      intro same
      apply different
      apply Fin.ext
      simpa using congrArg Fin.val same)

def priorNodeAt
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (position : step.base.val.NodeId) :
    step.prior.val.NodeId :=
  let count := counts.baseNodeCountAddOne
  Fin.cast count
    (restoreFin (Fin.cast count.symm step.priorApplication) position)

@[simp] theorem priorNodeAt_position
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (target : step.prior.val.NodeId)
    (different : target ≠ step.priorApplication) :
    priorNodeAt step counts
      (priorNodePosition step counts target different) = target := by
  apply Fin.ext
  simp [priorNodeAt, priorNodePosition]

theorem priorNodeAt_ne_application
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (position : step.base.val.NodeId) :
    priorNodeAt step counts position ≠ step.priorApplication := by
  intro same
  apply restoreFin_ne
    (Fin.cast counts.baseNodeCountAddOne.symm step.priorApplication) position
  apply Fin.ext
  simpa [priorNodeAt] using congrArg Fin.val same

@[simp] theorem priorNodePosition_at
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (position : step.base.val.NodeId) :
    priorNodePosition step counts (priorNodeAt step counts position)
        (priorNodeAt_ne_application step counts position) = position := by
  apply Fin.ext
  simp [priorNodeAt, priorNodePosition]

theorem priorNodeAt_injective
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step) :
    Function.Injective (priorNodeAt step counts) := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  simp only [priorNodeAt, Fin.val_cast] at values
  unfold restoreFin at values
  split at values <;> split at values <;>
    simp only [Fin.val_mk] at values <;> omega

/-- Direct checked allocation for one retained post-deletion node position. -/
def checkedRetainedNodeAtPosition
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (position : step.base.val.NodeId) :
    step.checked.val.NodeId :=
  ⟨position.val, by
    have baseCount := counts.baseNodeCountAddOne
    have checkedCount := counts.checkedNodeCountAddOne
    have positionBound := position.isLt
    omega⟩

def checkedRetainedNode
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (target : step.prior.val.NodeId)
    (different : target ≠ step.priorApplication) :
    step.checked.val.NodeId :=
  checkedRetainedNodeAtPosition step counts
    (priorNodePosition step counts target different)

/-- The constructive retained-node position is the raw erasure allocation. -/
theorem retained_allFin_index_eq_dropFin
    {count : Nat} (removed target : Fin (count + 1))
    (different : target ≠ removed) :
    ((indexOf?
        ((allFin (count + 1)).filter
          (fun value => decide (value ∉ [removed]))) target).get
        (indexOf?_isSome_iff.mpr (by simp [different]))).val =
      (dropFin removed target different).val := by
  let retained :=
    (allFin (count + 1)).filter
      (fun value => decide (value ∉ [removed]))
  have retainedNodup : retained.Nodup :=
    (allFin_nodup (count + 1)).filter _
  have retainedExact :
      retained = (allFin count).map (restoreFin removed) := by
    dsimp only [retained]
    simpa only [List.mem_singleton] using
      retained_allFin_eq_map_restoreFin count removed
  have lengthExact : retained.length = count := by
    rw [retainedExact]
    simp [allFin_eq_finRange]
  let position : Fin retained.length :=
    Fin.cast lengthExact.symm (dropFin removed target different)
  have getExact :
      retained.get position = target := by
    rw [List.get_of_eq retainedExact position]
    simpa [position, allFin_eq_finRange] using
      restoreFin_dropFin removed target different
  have indexExact :
      indexOf? retained target = some position := by
    rw [← getExact]
    exact indexOf?_get_eq_some_of_nodup retainedNodup _
  rw [Option.get_of_eq_some _ indexExact]
  simp [position]

theorem retained_allFin_index_eq_dropFin_cast
    {count whole : Nat} (countExact : count + 1 = whole)
    (removed target : Fin whole) (different : target ≠ removed) :
    ((indexOf?
        ((allFin whole).filter
          (fun value => decide (value ∉ [removed]))) target).get
        (indexOf?_isSome_iff.mpr (by simp [different]))).val =
      (dropFin (Fin.cast countExact.symm removed)
        (Fin.cast countExact.symm target) (by
          intro same
          apply different
          apply Fin.ext
          simpa using congrArg Fin.val same)).val := by
  subst whole
  simpa using retained_allFin_index_eq_dropFin removed target different

theorem retainedNodeAllocation_generic
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (target : step.prior.val.NodeId)
    (different : target ≠ step.priorApplication) :
    checkedRetainedNode step counts target different =
      step.checkedPriorNode target different := by
  apply Fin.ext
  rw [step.checkedPriorNode_val]
  simp only [checkedRetainedNode, checkedRetainedNodeAtPosition,
    priorNodePosition, Fin.val_mk, Fin.val_cast]
  unfold ConcreteDiagram.DenseErasure.eraseNodeIndex
  simpa [ConcreteDiagram.DenseErasure.retainedNodes,
    ConcreteDiagram.nodesList, List.mem_singleton] using
      (retained_allFin_index_eq_dropFin_cast
        counts.baseNodeCountAddOne step.priorApplication target different).symm

/-- Lift a broad node origin through one accepted construction step. -/
def liftNodeOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps →
    PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])
  | .inl node => .inl node
  | .inr ⟨occurrence, .inl node⟩ =>
      .inr ⟨Fin.cast (by simp) (Fin.castAdd 1 occurrence), .inl node⟩
  | .inr ⟨occurrence, .inr request⟩ =>
      .inr ⟨Fin.cast (by simp) (Fin.castAdd 1 occurrence),
        .inr (Fin.cast (by
          change (steps[occurrence.val]).attachment.identityRequests.length =
            ((steps ++ [step])[occurrence.val]).attachment.identityRequests.length
          rw [List.getElem_append_left occurrence.isLt]) request)⟩

/-- Introduce a copied fragment node at the newest occurrence. -/
def freshContentNodeOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId) :
    PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step]) :=
  .inr ⟨Fin.cast (by simp) (Fin.last steps.length), .inl node⟩

/-- Introduce an attachment-generated request node at the newest occurrence. -/
def freshRequestNodeOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length) :
    PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step]) :=
  .inr ⟨Fin.cast (by simp) (Fin.last steps.length),
    .inr (Fin.cast (by
      change step.attachment.identityRequests.length =
        ((steps ++ [step])[steps.length]).attachment.identityRequests.length
      exact congrArg
        (fun current : RelationJoinStep source dying content =>
          current.attachment.identityRequests.length)
        (List.getElem_concat_length rfl _).symm) request)⟩

theorem liftRegionOrigin_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (liftRegionOrigin (steps := steps) step) := by
  intro left right same
  cases left with
  | inl leftRegion =>
      cases right with
      | inl rightRegion => exact congrArg Sum.inl (Sum.inl.inj same)
      | inr rightOccurrence => cases same
  | inr leftOccurrence =>
      cases right with
      | inl rightRegion => cases same
      | inr rightOccurrence =>
          rcases leftOccurrence with ⟨leftIndex, leftRegion⟩
          rcases rightOccurrence with ⟨rightIndex, rightRegion⟩
          have sigmaSame := Sum.inr.inj same
          have indexSame : leftIndex = rightIndex := by
            apply Fin.ext
            simpa [liftRegionOrigin] using
              congrArg Fin.val (congrArg Sigma.fst sigmaSame)
          subst rightIndex
          have regionSame : leftRegion = rightRegion :=
            congrArg Sigma.snd sigmaSame
          subst rightRegion
          rfl

theorem liftRegionOrigin_ne_fresh
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    liftRegionOrigin step origin ≠ freshRegionOrigin step region := by
  intro same
  cases origin with
  | inl sourceRegion => cases same
  | inr occurrence =>
      have bound := occurrence.1.isLt
      have indexSame := congrArg (fun value => match value with
        | .inl _ => 0
        | .inr current => current.1.val) same
      simp [liftRegionOrigin, freshRegionOrigin] at indexSame
      omega

theorem freshRegionOrigin_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (freshRegionOrigin (steps := steps) step) := by
  intro left right same
  simpa [freshRegionOrigin] using same

theorem liftNodeOrigin_live
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (live : PrefixNodeLive (liftNodeOrigin step origin)) :
    PrefixNodeLive origin := by
  cases origin with
  | inl node =>
      intro member
      apply live
      simpa [PrefixNodeLive, liftNodeOrigin] using
        List.mem_append_left
          ([step].map RelationJoinStep.application) member
  | inr occurrence => trivial

theorem liftNodeOrigin_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (liftNodeOrigin (steps := steps) step) := by
  intro left right same
  cases left with
  | inl leftNode =>
      cases right with
      | inl rightNode => simpa [liftNodeOrigin] using same
      | inr rightOccurrence =>
          rcases rightOccurrence with ⟨rightIndex, rightNode⟩
          cases rightNode <;> simp [liftNodeOrigin] at same
  | inr leftOccurrence =>
      cases right with
      | inl rightNode =>
          rcases leftOccurrence with ⟨leftIndex, leftNode⟩
          cases leftNode <;> simp [liftNodeOrigin] at same
      | inr rightOccurrence =>
          rcases leftOccurrence with ⟨leftIndex, leftNode⟩
          rcases rightOccurrence with ⟨rightIndex, rightNode⟩
          cases leftNode with
          | inl leftContent =>
              cases rightNode with
              | inl rightContent =>
                  simp only [liftNodeOrigin, Sum.inr.injEq,
                    Sigma.mk.injEq] at same
                  have indexSame : leftIndex = rightIndex := by
                    apply Fin.ext
                    simpa using congrArg Fin.val same.1
                  subst rightIndex
                  have contentSame : leftContent = rightContent := by
                    simpa using eq_of_heq same.2
                  subst rightContent
                  rfl
              | inr rightRequest =>
                  simp [liftNodeOrigin] at same
                  have indexSame : leftIndex = rightIndex := by
                    apply Fin.ext
                    simpa using congrArg Fin.val same.1
                  subst rightIndex
                  cases eq_of_heq same.2
          | inr leftRequest =>
              cases rightNode with
              | inl rightContent =>
                  simp [liftNodeOrigin] at same
                  have indexSame : leftIndex = rightIndex := by
                    apply Fin.ext
                    simpa using congrArg Fin.val same.1
                  subst rightIndex
                  cases eq_of_heq same.2
              | inr rightRequest =>
                  simp only [liftNodeOrigin, Sum.inr.injEq,
                    Sigma.mk.injEq] at same
                  have indexSame : leftIndex = rightIndex := by
                    apply Fin.ext
                    simpa using congrArg Fin.val same.1
                  subst rightIndex
                  have castSame := Sum.inr.inj (eq_of_heq same.2)
                  have requestSame : leftRequest = rightRequest := by
                    apply Fin.ext
                    simpa using congrArg Fin.val castSame
                  subst rightRequest
                  rfl

theorem liftNodeOrigin_ne_freshContent
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (node : content.val.diagram.NodeId) :
    liftNodeOrigin step origin ≠ freshContentNodeOrigin step node := by
  intro same
  cases origin with
  | inl sourceNode => simp [liftNodeOrigin, freshContentNodeOrigin] at same
  | inr occurrence =>
      rcases occurrence with ⟨index, inner⟩
      cases inner <;> simp only [liftNodeOrigin] at same
      all_goals
        have bound := index.isLt
        have indexSame := congrArg (fun value => match value with
          | .inl _ => 0
          | .inr current => current.1.val + 1) same
        simp [freshContentNodeOrigin] at indexSame
        omega

theorem liftNodeOrigin_ne_freshRequest
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (request : Fin step.attachment.identityRequests.length) :
    liftNodeOrigin step origin ≠ freshRequestNodeOrigin step request := by
  intro same
  cases origin with
  | inl sourceNode => simp [liftNodeOrigin, freshRequestNodeOrigin] at same
  | inr occurrence =>
      rcases occurrence with ⟨index, inner⟩
      cases inner <;> simp only [liftNodeOrigin] at same
      all_goals
        have bound := index.isLt
        have indexSame := congrArg (fun value => match value with
          | .inl _ => 0
          | .inr current => current.1.val + 1) same
        simp [freshRequestNodeOrigin] at indexSame
        omega

theorem freshContentNodeOrigin_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (freshContentNodeOrigin (steps := steps) step) := by
  intro left right same
  simpa [freshContentNodeOrigin] using same

theorem freshRequestNodeOrigin_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (freshRequestNodeOrigin (steps := steps) step) := by
  intro left right same
  simp only [freshRequestNodeOrigin, Sum.inr.injEq,
    Sigma.mk.injEq] at same
  have castSame := Sum.inr.inj (eq_of_heq same.2)
  apply Fin.ext
  simpa using congrArg Fin.val castSame

theorem freshContentNodeOrigin_ne_request
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId)
    (request : Fin step.attachment.identityRequests.length) :
    freshContentNodeOrigin (steps := steps) step node ≠
      freshRequestNodeOrigin (steps := steps) step request := by
  intro same
  have tagSame := congrArg (fun origin => match origin with
    | .inl _ => true
    | .inr occurrence => match occurrence.2 with
      | .inl _ => true
      | .inr _ => false) same
  simpa [freshContentNodeOrigin, freshRequestNodeOrigin] using tagSame

abbrev RegionOriginView
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])) : Type :=
  (Σ priorOrigin : PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps,
    PLift (origin = liftRegionOrigin step priorOrigin)) ⊕
  (Σ region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root },
    PLift (origin = freshRegionOrigin step region))

def regionOriginView
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])) :
    RegionOriginView step origin := by
  cases origin with
  | inl region => exact .inl ⟨.inl region, ⟨rfl⟩⟩
  | inr occurrence =>
      rcases occurrence with ⟨index, region⟩
      by_cases last : index.val = steps.length
      · have indexExact :
            index = Fin.cast (by simp) (Fin.last steps.length) := by
          apply Fin.ext
          simpa using last
        subst index
        exact .inr ⟨region, ⟨by simp [freshRegionOrigin]⟩⟩
      · have priorBound : index.val < steps.length := by
          have bound := index.isLt
          simp at bound
          omega
        let priorIndex : Fin steps.length := ⟨index.val, priorBound⟩
        exact .inl ⟨.inr ⟨priorIndex, region⟩, ⟨by
          apply congrArg Sum.inr
          apply Sigma.ext
          · apply Fin.ext
            rfl
          · rfl⟩⟩

abbrev NodeOriginView
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])) : Type :=
  (Σ priorOrigin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps,
    PLift (origin = liftNodeOrigin step priorOrigin)) ⊕
  ((Σ node : content.val.diagram.NodeId,
      PLift (origin = freshContentNodeOrigin step node)) ⊕
    (Σ request : Fin step.attachment.identityRequests.length,
      PLift (origin = freshRequestNodeOrigin step request)))

def nodeOriginView
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])) :
    NodeOriginView step origin := by
  cases origin with
  | inl node => exact .inl ⟨.inl node, ⟨rfl⟩⟩
  | inr occurrence =>
      rcases occurrence with ⟨index, inner⟩
      by_cases last : index.val = steps.length
      · have indexExact :
            index = Fin.cast (by simp) (Fin.last steps.length) := by
          apply Fin.ext
          simpa using last
        subst index
        cases inner with
        | inl node =>
            exact .inr (.inl ⟨node, ⟨by
              simp [freshContentNodeOrigin]⟩⟩)
        | inr request =>
            let request' : Fin step.attachment.identityRequests.length :=
              Fin.cast (by
                change
                  ((steps ++ [step])[steps.length]).attachment.identityRequests.length =
                    step.attachment.identityRequests.length
                rw [List.getElem_concat_length]
                rfl) request
            exact .inr (.inr ⟨request', ⟨by
              simp [freshRequestNodeOrigin, request']⟩⟩)
      · have priorBound : index.val < steps.length := by
          have bound := index.isLt
          simp at bound
          omega
        let priorIndex : Fin steps.length := ⟨index.val, priorBound⟩
        cases inner with
        | inl node =>
            exact .inl ⟨.inr ⟨priorIndex, .inl node⟩, ⟨by
              apply congrArg Sum.inr
              apply Sigma.ext
              · apply Fin.ext
                rfl
              · rfl⟩⟩
        | inr request =>
            let request' :
                Fin ((steps.get priorIndex).attachment.identityRequests.length) :=
              Fin.cast (by
                apply congrArg (fun current :
                  RelationJoinStep source dying content =>
                    current.attachment.identityRequests.length)
                simp only [List.get_eq_getElem]
                rw [List.getElem_append_left priorBound]) request
            exact .inl ⟨.inr ⟨priorIndex, .inr request'⟩, ⟨by
              simp [liftNodeOrigin, request', priorIndex]⟩⟩

/-- The sole ordered region and live-node ledgers at one checked prefix. -/
structure AtlasRows
    (steps : List (RelationJoinStep source dying content))
    (current : CheckedDiagram definitions) : Type where
  regionRows : List (PrefixRegionOrigin (source := source) (dying := dying)
    (content := content) steps)
  regionLength : regionRows.length = current.val.regionCount
  nodeRows : List (PrefixNodeOrigin (source := source) (dying := dying)
    (content := content) steps)
  nodeLength : nodeRows.length = current.val.nodeCount

def AtlasRows.regionAt
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (rows : AtlasRows (source := source) (dying := dying)
      (content := content) steps current)
    (target : current.val.RegionId) :
    PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps :=
  rows.regionRows.get (Fin.cast rows.regionLength.symm target)

def AtlasRows.nodeAt
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (rows : AtlasRows (source := source) (dying := dying)
      (content := content) steps current)
    (target : current.val.NodeId) :
    PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps :=
  rows.nodeRows.get (Fin.cast rows.nodeLength.symm target)

private theorem listGet_injective_of_nodup [DecidableEq α]
    {values : List α} (nodup : values.Nodup) :
    Function.Injective values.get := by
  intro left right same
  apply Fin.ext
  have valuesSame : values[left.val]? = values[right.val]? := by
    rw [List.getElem?_eq_getElem left.isLt,
      List.getElem?_eq_getElem right.isLt]
    exact congrArg some same
  exact (List.getElem?_inj left.isLt nodup).mp valuesSame

theorem AtlasRows.regionAt_injective
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (rows : AtlasRows (source := source) (dying := dying)
      (content := content) steps current)
    (nodup : rows.regionRows.Nodup) : Function.Injective rows.regionAt := by
  intro left right same
  have castSame := listGet_injective_of_nodup nodup same
  apply Fin.ext
  simpa using congrArg Fin.val castSame

theorem AtlasRows.nodeAt_injective
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (rows : AtlasRows (source := source) (dying := dying)
      (content := content) steps current)
    (nodup : rows.nodeRows.Nodup) : Function.Injective rows.nodeAt := by
  intro left right same
  have castSame := listGet_injective_of_nodup nodup same
  apply Fin.ext
  simpa using congrArg Fin.val castSame

/-- A Type-valued exact-row region landing in the sole ledger. -/
structure RegionLands
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (rows : AtlasRows (source := source) (dying := dying)
      (content := content) steps current)
    (origin : PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps)
    (target : current.val.RegionId) : Type where
  exact : rows.regionAt target = origin

/-- A Type-valued exact-row node landing in the sole ledger. -/
structure NodeLands
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (rows : AtlasRows (source := source) (dying := dying)
      (content := content) steps current)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (target : current.val.NodeId) : Type where
  exact : rows.nodeAt target = origin

/-- One certified atlas value owned by an accepted construction prefix. -/
structure CertifiedAtlas
    (steps : List (RelationJoinStep source dying content))
    (current : CheckedDiagram definitions) : Type where
  rows : AtlasRows (source := source) (dying := dying)
    (content := content) steps current
  regionNodup : rows.regionRows.Nodup
  nodeNodup : rows.nodeRows.Nodup
  nodeRowsLive : ∀ target, PrefixNodeLive (rows.nodeAt target)
  locateRegion : ∀ origin, Σ target, RegionLands rows origin target
  locateNode : ∀ origin, PrefixNodeLive origin →
    Σ target, NodeLands rows origin target

/-- Source-region projection derived from the certified exact-row locator. -/
def CertifiedAtlas.regionImage
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (atlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps current)
    (region : source.val.RegionId) : current.val.RegionId :=
  (atlas.locateRegion (.inl region)).1

/-- Source-node projection derived from liveness and the exact-row locator. -/
def CertifiedAtlas.nodeImage
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (atlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps current)
    (node : source.val.NodeId) : Option current.val.NodeId :=
  if live : node ∉ steps.map RelationJoinStep.application then
    some (atlas.locateNode (.inl node) (by
      simpa [PrefixNodeLive] using live)).1
  else
    none

/-- The atlas omits exactly the source nodes consumed as applications by the
accepted raw construction prefix. -/
@[simp] theorem CertifiedAtlas.nodeImage_eq_none_iff
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (atlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps current)
    (node : source.val.NodeId) :
    atlas.nodeImage node = none ↔
      node ∈ steps.map RelationJoinStep.application := by
  simp [CertifiedAtlas.nodeImage]

/-- A successful source-node image is exactly the atlas row at its target. -/
def CertifiedAtlas.nodeImageLandsOfEqSome
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (atlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps current)
    (node : source.val.NodeId) (target : current.val.NodeId)
    (exact : atlas.nodeImage node = some target) :
    NodeLands atlas.rows (.inl node) target := by
  unfold CertifiedAtlas.nodeImage at exact
  split at exact
  · rename_i live
    simp only [Option.some.injEq] at exact
    subst target
    exact (atlas.locateNode (.inl node) (by
      simpa [PrefixNodeLive] using live)).2
  · contradiction

/-- Exact pre-transition agreements and concrete allocation bridges. -/
structure AtlasStepReceipt
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    : Type extends AtlasStepCounts step where
  priorRegionImageAgreement : step.priorRegionImage = prior.regionImage
  priorNodeImageAgreement : step.priorNodeImage = prior.nodeImage
  freshRegionAllocation : ∀ position,
    checkedFreshRegionAtPosition step position =
      step.checkedFragmentRegion
        (step.attachment.fragmentRegions.get position)
  retainedRegionAllocation : ∀ target,
    checkedRetainedRegion step target = step.checkedPriorRegion target
  retainedNodeAllocation : ∀ target different,
    checkedRetainedNode step toAtlasStepCounts target different =
      step.checkedPriorNode target different

theorem AtlasStepReceipt.checkedRetainedNode_eq_checkedPriorNode
    {steps : List (RelationJoinStep source dying content)}
    {step : RelationJoinStep source dying content}
    {prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior}
    (receipt : AtlasStepReceipt step prior)
    (target : step.prior.val.NodeId)
    (different : target ≠ step.priorApplication) :
    checkedRetainedNode step receipt.toAtlasStepCounts target different =
      step.checkedPriorNode target different :=
  receipt.retainedNodeAllocation target different

/-- Ordered source rows before the first construction step. -/
def initialRows : AtlasRows (source := source) (dying := dying)
    (content := content) [] source where
  regionRows := source.val.regionsList.map Sum.inl
  regionLength := by
    simp [ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange]
  nodeRows := source.val.nodesList.map Sum.inl
  nodeLength := by
    simp [ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange]

@[simp] theorem initialRows_regionAt
    (target : source.val.RegionId) :
    (initialRows (source := source) (dying := dying)
      (content := content)).regionAt target = .inl target := by
  simp [AtlasRows.regionAt, initialRows, ConcreteDiagram.regionsList,
    Data.Finite.allFin_eq_finRange]

@[simp] theorem initialRows_nodeAt
    (target : source.val.NodeId) :
    (initialRows (source := source) (dying := dying)
      (content := content)).nodeAt target = .inl target := by
  simp [AtlasRows.nodeAt, initialRows, ConcreteDiagram.nodesList,
    Data.Finite.allFin_eq_finRange]

/-- The certified source atlas before the first accepted step. -/
def initialAtlas : CertifiedAtlas (source := source) (dying := dying)
    (content := content) [] source where
  rows := initialRows
  regionNodup := by
    exact (Data.Finite.allFin_nodup _).map _ (by simp)
  nodeNodup := by
    exact (Data.Finite.allFin_nodup _).map _ (by simp)
  nodeRowsLive := by
    intro target
    simp [PrefixNodeLive]
  locateRegion := by
    intro origin
    cases origin with
    | inl region => exact ⟨region, ⟨by simp⟩⟩
    | inr occurrence => exact Fin.elim0 occurrence.1
  locateNode := by
    intro origin live
    cases origin with
    | inl node => exact ⟨node, ⟨by simp⟩⟩
    | inr occurrence => exact Fin.elim0 occurrence.1

/-- Nonrecursive ordered ledger extension for one accepted checked step. -/
def extendRows
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : AtlasRows (source := source) (dying := dying)
      (content := content) steps step.prior) :
    AtlasRows (source := source) (dying := dying) (content := content)
      (steps ++ [step]) step.checked := by
  let freshRegionRows :=
    (Data.Finite.allFin step.attachment.fragmentRegions.length).map
      (fun position => freshRegionOrigin (steps := steps) step
        (nonrootRegionAt position))
  let retainedRows :=
    (Data.Finite.allFin step.base.val.nodeCount).map fun position =>
      liftNodeOrigin step (prior.nodeAt (priorNodeAt step counts position))
  let contentRows := content.val.diagram.nodesList.map
    (freshContentNodeOrigin (steps := steps) step)
  let requestRows :=
    (Data.Finite.allFin step.attachment.identityRequests.length).map
      (freshRequestNodeOrigin (steps := steps) step)
  refine
    { regionRows := prior.regionRows.map (liftRegionOrigin step) ++
        freshRegionRows
      regionLength := ?_
      nodeRows := retainedRows ++ contentRows ++ requestRows
      nodeLength := ?_ }
  · rw [List.length_append, List.length_map, step.checked_regionCount,
      prior.regionLength]
    simp only [freshRegionRows, List.length_map,
      Data.Finite.allFin_eq_finRange]
    exact congrArg (Nat.add step.prior.val.regionCount)
      (List.length_finRange (n := step.attachment.fragmentRegions.length))
  · have baseCount := counts.baseNodeCountAddOne
    have checkedCount := counts.checkedNodeCountAddOne
    simp only [retainedRows, contentRows, requestRows, List.length_append,
      List.length_map, ConcreteDiagram.nodesList,
      Data.Finite.allFin_eq_finRange, List.length_finRange]
    omega

@[simp] theorem extendRows_regionAt_prior
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : AtlasRows (source := source) (dying := dying)
      (content := content) steps step.prior)
    (target : step.prior.val.RegionId) :
    (extendRows step counts prior).regionAt
        (checkedRetainedRegion step target) =
      liftRegionOrigin step (prior.regionAt target) := by
  simp only [AtlasRows.regionAt, extendRows, checkedRetainedRegion]
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by
    simpa [prior.regionLength] using target.isLt)]
  simp

@[simp] theorem extendRows_regionAt_fresh
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : AtlasRows (source := source) (dying := dying)
      (content := content) steps step.prior)
    (position : Fin step.attachment.fragmentRegions.length) :
    (extendRows step counts prior).regionAt
        (checkedFreshRegionAtPosition step position) =
      freshRegionOrigin step (nonrootRegionAt position) := by
  have priorCount := prior.regionLength
  simp [AtlasRows.regionAt, extendRows, checkedFreshRegionAtPosition,
    List.get_eq_getElem]
  rw [List.getElem_append_right (by
    simp only [List.length_map]
    omega)]
  rw [List.getElem_map]
  have offset : step.prior.val.regionCount + position.val -
      (prior.regionRows.map (liftRegionOrigin step)).length =
        position.val := by
    simp only [List.length_map]
    omega
  simp only [offset]
  simp only [Data.Finite.allFin_eq_finRange]
  apply congrArg (fun current =>
    freshRegionOrigin step (nonrootRegionAt current))
  apply Fin.ext
  have finRangeExact := List.getElem_finRange
    (n := step.attachment.fragmentRegions.length)
    (i := position.val) (by simpa using position.isLt)
  simpa only [Fin.val_cast, Fin.val_mk] using
    congrArg Fin.val finRangeExact

@[simp] theorem extendRows_nodeAt_prior
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : AtlasRows (source := source) (dying := dying)
      (content := content) steps step.prior)
    (target : step.prior.val.NodeId)
    (different : target ≠ step.priorApplication) :
    (extendRows step counts prior).nodeAt
        (checkedRetainedNode step counts target different) =
      liftNodeOrigin step (prior.nodeAt target) := by
  let position := priorNodePosition step counts target different
  simp only [AtlasRows.nodeAt, extendRows, checkedRetainedNode,
    checkedRetainedNodeAtPosition, List.get_eq_getElem]
  rw [List.getElem_append_left (by
    have bound := position.isLt
    simp [Data.Finite.allFin_eq_finRange]
    omega)]
  rw [List.getElem_append_left (by
    simpa [Data.Finite.allFin_eq_finRange] using position.isLt)]
  rw [List.getElem_map]
  apply congrArg (liftNodeOrigin step)
  apply congrArg prior.nodeAt
  have positionSame :
      (Data.Finite.allFin step.base.val.nodeCount)[position.val]'(by
        simpa [Data.Finite.allFin_eq_finRange] using position.isLt) =
        position := by
    apply Fin.ext
    have finRangeExact := List.getElem_finRange
      (n := step.base.val.nodeCount) (i := position.val)
      (by simpa [Data.Finite.allFin_eq_finRange] using position.isLt)
    simpa only [Data.Finite.allFin_eq_finRange, Fin.val_cast, Fin.val_mk]
      using congrArg Fin.val finRangeExact
  exact (congrArg (priorNodeAt step counts) positionSame).trans
    (priorNodeAt_position step counts target different)

@[simp] theorem extendRows_nodeAt_content
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : AtlasRows (source := source) (dying := dying)
      (content := content) steps step.prior)
    (node : content.val.diagram.NodeId) :
    (extendRows step counts prior).nodeAt (step.checkedFragmentNode node) =
      freshContentNodeOrigin step node := by
  simp [AtlasRows.nodeAt, extendRows,
    ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange,
    List.get_eq_getElem, List.length_ofFn]

@[simp] theorem extendRows_nodeAt_request
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : AtlasRows (source := source) (dying := dying)
      (content := content) steps step.prior)
    (request : Fin step.attachment.identityRequests.length) :
    (extendRows step counts prior).nodeAt (step.checkedIdentityNode request) =
      freshRequestNodeOrigin step request := by
  have retainedCount := List.length_finRange (n := step.base.val.nodeCount)
  simp [AtlasRows.nodeAt, extendRows,
    ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange,
    List.get_eq_getElem, List.length_ofFn]
  rw [List.getElem_append_right (by
    simp only [List.length_map, List.length_ofFn]
    omega)]
  rw [List.getElem_append_right (by
    simp only [List.length_map, List.length_ofFn, List.length_finRange]
    omega)]
  rw [List.getElem_map]
  congr 1
  apply Fin.ext
  simp only [List.getElem_finRange, Fin.val_cast, Fin.val_mk,
    List.length_map, List.length_finRange, List.length_ofFn]
  omega

theorem extendRows_regionNodup
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior) :
    (extendRows step counts prior.rows).regionRows.Nodup := by
  let freshRows :=
    (Data.Finite.allFin step.attachment.fragmentRegions.length).map
      (fun position => freshRegionOrigin (steps := steps) step
        (nonrootRegionAt position))
  change (prior.rows.regionRows.map (liftRegionOrigin step) ++
    freshRows).Nodup
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact prior.regionNodup.map _ (by
      intro left right different same
      exact different (liftRegionOrigin_injective step same))
  · exact (Data.Finite.allFin_nodup _).map _ (by
      intro left right different same
      apply different
      apply nonrootRegionAt_injective
      exact freshRegionOrigin_injective step same)
  · intro priorOrigin priorMember freshOrigin freshMember same
    rcases List.mem_map.mp priorMember with ⟨origin, _, rfl⟩
    rcases List.mem_map.mp freshMember with ⟨position, _, rfl⟩
    exact liftRegionOrigin_ne_fresh step origin _ same

theorem extendRows_nodeNodup
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior) :
    (extendRows step counts prior.rows).nodeRows.Nodup := by
  let retainedRows :=
    (Data.Finite.allFin step.base.val.nodeCount).map fun position =>
      liftNodeOrigin step
        (prior.rows.nodeAt (priorNodeAt step counts position))
  let contentRows := content.val.diagram.nodesList.map
    (freshContentNodeOrigin (steps := steps) step)
  let requestRows :=
    (Data.Finite.allFin step.attachment.identityRequests.length).map
      (freshRequestNodeOrigin (steps := steps) step)
  change (retainedRows ++ contentRows ++ requestRows).Nodup
  have retainedNodup : retainedRows.Nodup :=
    (Data.Finite.allFin_nodup _).map _ (by
      intro left right different same
      apply different
      apply priorNodeAt_injective step counts
      apply prior.rows.nodeAt_injective prior.nodeNodup
      exact liftNodeOrigin_injective step same)
  have contentNodup : contentRows.Nodup :=
    (Data.Finite.allFin_nodup _).map _ (by
      intro left right different same
      exact different (freshContentNodeOrigin_injective step same))
  have requestNodup : requestRows.Nodup :=
    (Data.Finite.allFin_nodup _).map _ (by
      intro left right different same
      exact different (freshRequestNodeOrigin_injective step same))
  rw [List.nodup_append]
  refine ⟨?_, requestNodup, ?_⟩
  · rw [List.nodup_append]
    refine ⟨retainedNodup, contentNodup, ?_⟩
    intro retained retainedMember fresh freshMember same
    rcases List.mem_map.mp retainedMember with ⟨position, _, rfl⟩
    rcases List.mem_map.mp freshMember with ⟨node, _, rfl⟩
    exact liftNodeOrigin_ne_freshContent step _ node same
  · intro earlier earlierMember fresh freshMember same
    rcases List.mem_append.mp earlierMember with retainedMember | contentMember
    · rcases List.mem_map.mp retainedMember with ⟨position, _, rfl⟩
      rcases List.mem_map.mp freshMember with ⟨request, _, rfl⟩
      exact liftNodeOrigin_ne_freshRequest step _ request same
    · rcases List.mem_map.mp contentMember with ⟨node, _, rfl⟩
      rcases List.mem_map.mp freshMember with ⟨request, _, rfl⟩
      exact freshContentNodeOrigin_ne_request step node request same

theorem liftedPriorRow_live
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (applicationLanding : NodeLands prior.rows (.inl step.application)
      step.priorApplication)
    (position : step.base.val.NodeId) :
    PrefixNodeLive
      (liftNodeOrigin step
        (prior.rows.nodeAt (priorNodeAt step counts position))) := by
  have priorLive := prior.nodeRowsLive (priorNodeAt step counts position)
  cases rowExact : prior.rows.nodeAt (priorNodeAt step counts position) with
  | inl node =>
      simp only [PrefixNodeLive, liftNodeOrigin, List.map_append,
        List.map_singleton, List.mem_append, List.mem_singleton, not_or]
      refine ⟨?_, ?_⟩
      · simpa [PrefixNodeLive, rowExact] using priorLive
      · intro nodeExact
        subst node
        have targetSame := prior.rows.nodeAt_injective prior.nodeNodup
          (rowExact.trans applicationLanding.exact.symm)
        exact priorNodeAt_ne_application step counts position targetSame
  | inr occurrence =>
      rcases occurrence with ⟨index, inner⟩
      cases inner <;> simp [PrefixNodeLive, liftNodeOrigin]

theorem extendRows_nodeLive
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (applicationLanding : NodeLands prior.rows (.inl step.application)
      step.priorApplication)
    (target : step.checked.val.NodeId) :
    PrefixNodeLive ((extendRows step counts prior.rows).nodeAt target) := by
  have member : (extendRows step counts prior.rows).nodeAt target ∈
      (extendRows step counts prior.rows).nodeRows := by
    exact List.get_mem _ _
  simp only [extendRows] at member ⊢
  rcases List.mem_append.mp member with earlierMember | requestMember
  · rcases List.mem_append.mp earlierMember with
      retainedMember | contentMember
    · rcases List.mem_map.mp retainedMember with
        ⟨position, _, rowExact⟩
      rw [← rowExact]
      exact liftedPriorRow_live step counts prior applicationLanding position
    · rcases List.mem_map.mp contentMember with ⟨node, _, rowExact⟩
      rw [← rowExact]
      simp [PrefixNodeLive, freshContentNodeOrigin]
  · rcases List.mem_map.mp requestMember with ⟨request, _, rowExact⟩
    rw [← rowExact]
    simp [PrefixNodeLive, freshRequestNodeOrigin]

def locateRegionAfterStep
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (origin : PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])) :
    Σ target, RegionLands (extendRows step counts prior.rows) origin target := by
  rcases regionOriginView step origin with priorCase | freshCase
  · rcases priorCase with ⟨priorOrigin, ⟨originExact⟩⟩
    subst origin
    obtain ⟨target, landing⟩ := prior.locateRegion priorOrigin
    exact ⟨checkedRetainedRegion step target, ⟨by
      rw [extendRows_regionAt_prior]
      exact congrArg (liftRegionOrigin step) landing.exact⟩⟩
  · rcases freshCase with ⟨region, ⟨originExact⟩⟩
    subst origin
    exact ⟨checkedFreshRegionAtPosition step
        (nonrootRegionPosition region), ⟨by
      rw [extendRows_regionAt_fresh]
      rw [nonrootRegionAt_position]⟩⟩

def locateNodeAfterStep
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (counts : AtlasStepCounts step)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (applicationLanding : NodeLands prior.rows (.inl step.application)
      step.priorApplication)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step]))
    (live : PrefixNodeLive origin) :
    Σ target, NodeLands (extendRows step counts prior.rows) origin target := by
  rcases nodeOriginView step origin with priorCase | freshCase
  · rcases priorCase with ⟨priorOrigin, ⟨originExact⟩⟩
    subst origin
    have priorLive := liftNodeOrigin_live step priorOrigin live
    obtain ⟨target, landing⟩ := prior.locateNode priorOrigin priorLive
    have different : target ≠ step.priorApplication := by
      intro targetExact
      subst target
      have priorOriginExact : priorOrigin = .inl step.application :=
        landing.exact.symm.trans applicationLanding.exact
      subst priorOrigin
      have stillLive : step.application ∉
          (steps ++ [step]).map RelationJoinStep.application := by
        simpa [PrefixNodeLive, liftNodeOrigin] using live
      exact stillLive (by simp)
    exact ⟨checkedRetainedNode step counts target different, ⟨by
      rw [extendRows_nodeAt_prior]
      exact congrArg (liftNodeOrigin step) landing.exact⟩⟩
  · rcases freshCase with contentCase | requestCase
    · rcases contentCase with ⟨node, ⟨originExact⟩⟩
      subst origin
      exact ⟨step.checkedFragmentNode node, ⟨by
        rw [extendRows_nodeAt_content]⟩⟩
    · rcases requestCase with ⟨request, ⟨originExact⟩⟩
      subst origin
      exact ⟨step.checkedIdentityNode request, ⟨by
        rw [extendRows_nodeAt_request]⟩⟩

/-- Certified nonrecursive atlas extension for one accepted checked step. -/
def extendAtlas
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step prior)
    (applicationLanding : NodeLands prior.rows (.inl step.application)
      step.priorApplication) :
    CertifiedAtlas (source := source) (dying := dying) (content := content)
      (steps ++ [step]) step.checked where
  rows := extendRows step receipt.toAtlasStepCounts prior.rows
  regionNodup := extendRows_regionNodup step receipt.toAtlasStepCounts prior
  nodeNodup := extendRows_nodeNodup step receipt.toAtlasStepCounts prior
  nodeRowsLive := extendRows_nodeLive step receipt.toAtlasStepCounts prior
    applicationLanding
  locateRegion := locateRegionAfterStep step receipt.toAtlasStepCounts prior
  locateNode := locateNodeAfterStep step receipt.toAtlasStepCounts prior
    applicationLanding

/-- The extended atlas derives exactly the checked source-region image. -/
theorem extendAtlas_regionImageAgreement
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step prior)
    (applicationLanding : NodeLands prior.rows (.inl step.application)
      step.priorApplication) :
    (extendAtlas step prior receipt applicationLanding).regionImage =
      step.checkedRegionImage := by
  symm
  funext region
  rw [step.checkedRegionImage_eq_checkedPriorRegion]
  rw [congrFun receipt.priorRegionImageAgreement region]
  rw [← receipt.retainedRegionAllocation (prior.regionImage region)]
  rfl

/-- The extended atlas derives exactly the checked partial source-node image. -/
theorem extendAtlas_nodeImageAgreement
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step prior)
    (applicationLanding : NodeLands prior.rows (.inl step.application)
      step.priorApplication) :
    (extendAtlas step prior receipt applicationLanding).nodeImage =
      step.checkedNodeImage := by
  funext sourceNode
  by_cases consumed : sourceNode = step.application
  · subst sourceNode
    rw [step.checkedNodeImage_application]
    simp [CertifiedAtlas.nodeImage]
  · by_cases priorConsumed :
        sourceNode ∈ steps.map RelationJoinStep.application
    · have priorAtlasNone : prior.nodeImage sourceNode = none := by
        simp [CertifiedAtlas.nodeImage, priorConsumed]
      have priorNone : step.priorNodeImage sourceNode = none := by
        rw [receipt.priorNodeImageAgreement]
        exact priorAtlasNone
      have checkedNone : step.checkedNodeImage sourceNode = none := by
        rw [step.checkedNodeImageExact, step.baseNodeImageExact, priorNone]
        rfl
      rw [checkedNone]
      simp [CertifiedAtlas.nodeImage, priorConsumed]
    · let priorLanding := prior.locateNode (.inl sourceNode) (by
        simpa [PrefixNodeLive] using priorConsumed)
      let priorTarget := priorLanding.1
      have priorAtlasExact :
          prior.nodeImage sourceNode = some priorTarget := by
        simp [CertifiedAtlas.nodeImage, priorConsumed, priorTarget, priorLanding]
      have priorExact :
          step.priorNodeImage sourceNode = some priorTarget := by
        rw [receipt.priorNodeImageAgreement]
        exact priorAtlasExact
      have different : priorTarget ≠ step.priorApplication := by
        intro targetExact
        have rowExact := priorLanding.2.exact
        change prior.rows.nodeAt priorTarget = .inl sourceNode at rowExact
        rw [targetExact, applicationLanding.exact] at rowExact
        exact consumed (Sum.inl.inj rowExact.symm)
      have extendedLive :
          sourceNode ∉ (steps ++ [step]).map
            RelationJoinStep.application := by
        simp [priorConsumed, consumed]
      rw [step.checkedNodeImage_of_prior priorExact different]
      simp only [CertifiedAtlas.nodeImage]
      rw [dif_pos extendedLive]
      change some (checkedRetainedNode step receipt.toAtlasStepCounts
          priorTarget _) =
        some (step.checkedPriorNode priorTarget different)
      exact congrArg some
        (receipt.checkedRetainedNode_eq_checkedPriorNode priorTarget _)

end ConcreteWireQuantifier

end VisualProof
