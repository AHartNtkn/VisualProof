import VisualProof.Rule.MonolithicWireQuantifierRawNodeTrace

namespace VisualProof

namespace MonolithicWireQuantifier

open _root_.VisualProof.ConcreteWireQuantifier
open ConcreteWireQuantifier.RelationJoinConstructionTrace

universe u

section Origins

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

/-- Allocation-neutral origins of raw joined regions.  A content root is not
fresh: it resolves to the retained source region hosting that occurrence. -/
abbrev RelationJoinRawRegionOrigin
    (result : RelationJoinResult source dying content parameters) :=
  RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
    (content := content) result.steps

/-- Final raw-node origins are exactly the live broad origins retained by the
terminal construction ledger. -/
abbrev RelationJoinRawNodeOrigin
    (result : RelationJoinResult source dying content parameters) :=
  { origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) result.steps //
    RelationJoinPrefixNodeLive origin }

/-- Allocation-neutral origins of raw joined wires.  Boundary content wires
are represented by their attachment's retained representative source wire. -/
abbrev RelationJoinRawWireOrigin
    (result : RelationJoinResult source dying content parameters) :=
  { wire : source.val.WireId // wire ≠ dying } ⊕
    Σ _occurrence : Fin result.steps.length,
      { wire : content.val.diagram.WireId //
        wire ∉ content.val.boundary }

/-- Exact construction-prefix region origins in concrete allocation order.
Each snoc lifts the retained prefix and then appends that occurrence's fresh
non-root content regions. -/
def relationJoinConstructionRegionOrigins {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    List (RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps) :=
  match trace with
  | .nil => source.val.regionsList.map Sum.inl
  | .snoc trace step _ _ _ _ _ _ _ _ =>
      (relationJoinConstructionRegionOrigins trace).map
          (prefixRegionOriginLift step) ++
        step.attachment.fragmentRegions.attach.map fun region =>
          prefixRegionFreshOrigin step
              ⟨region.1, by
                have member := List.mem_filter.mp region.2
                exact of_decide_eq_true member.2⟩

/-- Exact raw-region origins in construction-owned allocation order. -/
def relationJoinRawRegionOrigins
    (result : RelationJoinResult source dying content parameters) :
    List (RelationJoinRawRegionOrigin result) :=
  relationJoinConstructionRegionOrigins result.construction_trace

/-- Classify one terminal dense target by reading the sole construction node
ledger and packaging the liveness proved for that exact row. -/
def rawNodeOriginAt
    (result : RelationJoinResult source dying content parameters)
    (target : result.plainFinal.val.NodeId) :
    RelationJoinRawNodeOrigin result :=
  let boundTarget : result.boundFinal.val.NodeId :=
    Fin.cast result.plainFinal_nodeCount target
  let origin :=
    (relationJoinConstructionNodeOrigins result.construction_trace).get
      (Fin.cast
        (relationJoinConstructionNodeOrigins_length
          result.construction_trace).symm boundTarget)
  ⟨origin, relationJoinConstructionNodeOrigins_live
    result.construction_trace origin (List.get_mem _ _)⟩

/-- The target-led classifier carries the exact ledger landing it reads. -/
def rawNodeOriginAt_lands
    (result : RelationJoinResult source dying content parameters)
    (target : result.plainFinal.val.NodeId) :
    PrefixNodeLands result.construction_trace
      (rawNodeOriginAt result target).1
      (Fin.cast result.plainFinal_nodeCount target) := by
  exact ⟨rfl⟩

/-- A terminal node landing is a checked construction-ledger landing followed
by the node-preserving exhausted-wire deletion. -/
structure PlainPrefixNodeLands
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawNodeOrigin result)
    (target : result.plainFinal.val.NodeId) : Type where
  boundTarget : result.boundFinal.val.NodeId
  boundLanding : PrefixNodeLands result.construction_trace origin.1 boundTarget
  targetExact : target = result.plainBoundNodeImage boundTarget

/-- Every live terminal origin has a construction-derived plain landing. -/
def plainPrefixNodeLands_total
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawNodeOrigin result) :
    Σ target, PlainPrefixNodeLands result origin target := by
  obtain ⟨boundTarget, boundLanding⟩ := prefixNodeLands_total
    result.construction_trace origin.1 origin.2
  exact ⟨result.plainBoundNodeImage boundTarget,
    ⟨boundTarget, boundLanding, rfl⟩⟩

/-- A live terminal origin has only one plain landing. -/
theorem plainPrefixNodeLands_functional
    (result : RelationJoinResult source dying content parameters)
    {origin : RelationJoinRawNodeOrigin result}
    {left right : result.plainFinal.val.NodeId}
    (leftLanding : PlainPrefixNodeLands result origin left)
    (rightLanding : PlainPrefixNodeLands result origin right) :
    left = right := by
  rcases leftLanding with ⟨leftBound, leftPrefix, leftExact⟩
  rcases rightLanding with ⟨rightBound, rightPrefix, rightExact⟩
  exact leftExact.trans ((congrArg result.plainBoundNodeImage
    (prefixNodeLands_functional leftPrefix rightPrefix)).trans rightExact.symm)

/-- One terminal plain target has only one live origin. -/
theorem plainPrefixNodeLands_injective
    (result : RelationJoinResult source dying content parameters)
    {leftOrigin rightOrigin : RelationJoinRawNodeOrigin result}
    {target : result.plainFinal.val.NodeId}
    (leftLanding : PlainPrefixNodeLands result leftOrigin target)
    (rightLanding : PlainPrefixNodeLands result rightOrigin target) :
    leftOrigin = rightOrigin := by
  rcases leftLanding with ⟨leftBound, leftPrefix, leftExact⟩
  rcases rightLanding with ⟨rightBound, rightPrefix, rightExact⟩
  have boundExact := result.plainBoundNodeImage_injective
    (leftExact.symm.trans rightExact)
  subst rightBound
  apply Subtype.ext
  exact prefixNodeLands_injective leftPrefix rightPrefix

/-- The target-led classifier carries its terminal plain landing. -/
def rawNodeOriginAt_plain_lands
    (result : RelationJoinResult source dying content parameters)
    (target : result.plainFinal.val.NodeId) :
    PlainPrefixNodeLands result (rawNodeOriginAt result target) target := by
  let boundTarget : result.boundFinal.val.NodeId :=
    Fin.cast result.plainFinal_nodeCount target
  refine ⟨boundTarget, rawNodeOriginAt_lands result target, ?_⟩
  apply Fin.ext
  simp [boundTarget]

/-- Distinct terminal dense targets read distinct rows from the nodup ledger. -/
theorem rawNodeOriginAt_injective
    (result : RelationJoinResult source dying content parameters) :
    Function.Injective (rawNodeOriginAt result) := by
  intro left right same
  have originSame := congrArg Subtype.val same
  have rightLanding : PrefixNodeLands result.construction_trace
      (rawNodeOriginAt result left).1
      (Fin.cast result.plainFinal_nodeCount right) :=
    ⟨(rawNodeOriginAt_lands result right).exact.trans originSame.symm⟩
  have targetSame := prefixNodeLands_functional
    (rawNodeOriginAt_lands result left) rightLanding
  apply Fin.ext
  simpa using congrArg Fin.val targetSame

/-- Exact raw-node origins in terminal dense-target order. -/
def relationJoinRawNodeOrigins
    (result : RelationJoinResult source dying content parameters) :
    List (RelationJoinRawNodeOrigin result) :=
  result.plainFinal.val.nodesList.map (rawNodeOriginAt result)

/-- Exact raw-wire origins in concrete allocation order. -/
def relationJoinRawWireOrigins
    (result : RelationJoinResult source dying content parameters) :
    List (RelationJoinRawWireOrigin result) :=
  (((source.val.wiresList.filter fun wire => decide (wire ≠ dying)).attach.map
      fun wire =>
        ⟨wire.1, of_decide_eq_true (List.mem_filter.mp wire.2).2⟩).map
          Sum.inl) ++
    ((Data.Finite.allFin result.steps.length).flatMap fun occurrence =>
      ((result.steps.get occurrence).attachment.fragmentInternalWires.attach.map
        fun wire =>
          ⟨occurrence,
            ⟨wire.1, by
              have member := List.mem_filter.mp wire.2
              exact of_decide_eq_true member.2⟩⟩)).map Sum.inr

private theorem nodup_of_map_nodup
    (mapping : α → β) (values : List α)
    (mappedNodup : (values.map mapping).Nodup) :
    values.Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.map_cons, List.nodup_cons] at mappedNodup
      rw [List.nodup_cons]
      refine ⟨?_, induction mappedNodup.2⟩
      intro member
      exact mappedNodup.1 (List.mem_map.mpr ⟨_, member, rfl⟩)

private theorem attach_nodup_of_nodup
    (values : List α) (nodup : values.Nodup) :
    values.attach.Nodup := by
  apply nodup_of_map_nodup Subtype.val values.attach
  change values.attach.unattach.Nodup
  rw [List.unattach_attach]
  exact nodup

private theorem flatMap_nodup_of_disjoint
    {values : List α} {parts : α → List β}
    (valuesNodup : values.Nodup)
    (partsNodup : ∀ value ∈ values, (parts value).Nodup)
    (disjoint : ∀ left ∈ values, ∀ right ∈ values, left ≠ right →
      ∀ first ∈ parts left, ∀ second ∈ parts right, first ≠ second) :
    (values.flatMap parts).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at valuesNodup
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨partsNodup head (by simp), ?_, ?_⟩
      · exact induction valuesNodup.2
          (by intro value member; exact partsNodup value (by simp [member]))
          (by
            intro left leftMember right rightMember different
            exact disjoint left (by simp [leftMember]) right
              (by simp [rightMember]) different)
      · intro first firstMember second secondMember
        obtain ⟨right, rightMember, secondMember⟩ :=
          List.mem_flatMap.mp secondMember
        exact disjoint head (by simp) right (by simp [rightMember])
          (by intro same; subst right; exact valuesNodup.1 rightMember)
          first firstMember second secondMember

private theorem sumEnumerations_nodup
    (left : List α) (right : List β)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (left.map Sum.inl ++ right.map Sum.inr).Nodup := by
  rw [List.nodup_append]
  refine ⟨leftNodup.map _ (by simp), rightNodup.map _ (by simp), ?_⟩
  intro first firstMember second secondMember same
  rcases List.mem_map.mp firstMember with ⟨leftValue, _, rfl⟩
  rcases List.mem_map.mp secondMember with ⟨rightValue, _, rfl⟩
  contradiction

theorem relationJoinConstructionRegionOrigins_nodup {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    (relationJoinConstructionRegionOrigins trace).Nodup := by
  induction trace with
  | nil =>
      exact (Data.Finite.allFin_nodup _).map _ (by simp)
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      rw [relationJoinConstructionRegionOrigins, List.nodup_append]
      refine ⟨induction.map _ (by
        intro left right different same
        exact different (prefixRegionOriginLift_injective step same)), ?_, ?_⟩
      · exact (attach_nodup_of_nodup _
          ((Data.Finite.allFin_nodup _).filter _)).map _ (by
            intro left right different equality
            apply different
            apply Subtype.ext
            exact congrArg
              (fun region : { region : content.val.diagram.RegionId //
                region ≠ content.val.diagram.root } => region.1)
              (prefixRegionFreshOrigin_injective step equality))
      · intro prior priorMember fresh freshMember equality
        rcases List.mem_map.mp priorMember with
          ⟨priorOrigin, _, rfl⟩
        rcases List.mem_map.mp freshMember with
          ⟨freshRegion, _, rfl⟩
        exact prefixRegionOriginLift_ne_fresh step priorOrigin _ equality

theorem relationJoinConstructionRegionOrigins_complete {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) steps) :
    origin ∈ relationJoinConstructionRegionOrigins trace := by
  induction trace with
  | nil =>
      cases origin with
      | inl region =>
          simp [relationJoinConstructionRegionOrigins,
            ConcreteDiagram.regionsList, Data.Finite.mem_allFin]
      | inr occurrence => exact Fin.elim0 occurrence.1
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      rw [relationJoinConstructionRegionOrigins, List.mem_append]
      rcases prefixRegionOrigin_cases step origin with
        ⟨priorOrigin, rfl⟩ | ⟨freshRegion, rfl⟩
      · exact Or.inl (List.mem_map.mpr
          ⟨priorOrigin, induction priorOrigin, rfl⟩)
      · apply Or.inr
        apply List.mem_map.mpr
        let attached :
            { region // region ∈ step.attachment.fragmentRegions } :=
          ⟨freshRegion.1, by
            simp [ConcreteSpliceAttachment.fragmentRegions,
              ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
              freshRegion.2]⟩
        exact ⟨attached, by simp [attached], by
          apply congrArg (prefixRegionFreshOrigin step)
          apply Subtype.ext
          rfl⟩

theorem relationJoinConstructionRegionOrigins_length {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    final.val.regionCount =
      (relationJoinConstructionRegionOrigins trace).length := by
  induction trace with
  | nil => simp [relationJoinConstructionRegionOrigins,
      ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange]
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst priorExact
      rw [step.checked_regionCount, relationJoinConstructionRegionOrigins,
        List.length_append, List.length_map, List.length_map,
        List.length_attach, induction]

/-- Every construction landing indexes the matching row in the authoritative
construction enumeration. -/
theorem relationJoinConstructionRegionOrigins_landing_exact {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    {trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope}
    {origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps}
    {target : final.val.RegionId}
    (landing : PrefixRegionLands trace origin target) :
    (relationJoinConstructionRegionOrigins trace).get
        (Fin.cast (relationJoinConstructionRegionOrigins_length trace) target) =
      origin := by
  induction trace with
  | nil =>
      rcases landing with ⟨region, rfl, rfl⟩
      simp [relationJoinConstructionRegionOrigins,
        ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange]
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst_vars
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      rcases landing with prior | fresh
      · rcases prior with
          ⟨priorOrigin, priorTarget, priorLanding, rfl, rfl⟩
        have priorBound : priorTarget.val <
            ((relationJoinConstructionRegionOrigins trace).map
              (prefixRegionOriginLift step)).length := by
          rw [List.length_map,
            ← relationJoinConstructionRegionOrigins_length trace]
          exact priorTarget.isLt
        change
          ((relationJoinConstructionRegionOrigins trace).map
              (prefixRegionOriginLift step) ++
            _)[priorTarget.val]'(by
              rw [List.length_append]
              omega) =
          prefixRegionOriginLift step priorOrigin
        rw [List.getElem_append_left priorBound]
        simp only [List.getElem_map]
        exact congrArg (prefixRegionOriginLift step)
          (induction priorLanding)
      · rcases fresh with ⟨region, rfl, rfl⟩
        have regionMember :
            region.1 ∈ step.attachment.fragmentRegions := by
          simp [ConcreteSpliceAttachment.fragmentRegions,
            ConcreteDiagram.regionsList, Data.Finite.mem_allFin, region.2]
        simp [relationJoinConstructionRegionOrigins,
          RelationJoinStep.checkedFragmentRegion,
          ConcreteSpliceAttachment.fragmentRegion, region.2,
          ConcreteSpliceAttachment.freshRegion,
          relationJoinConstructionRegionOrigins_length trace,
          step.base_regionCount]
        apply congrArg (prefixRegionFreshOrigin step)
        apply Subtype.ext
        exact DenseList.get_index _ _ regionMember

/-- Retained source regions remain the exact leading rows of every
construction-owned origin enumeration. -/
theorem relationJoinConstructionRegionOrigins_source_prefix {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    source.val.regionsList.map
        (fun region => (Sum.inl region : RelationJoinPrefixRegionOrigin
          (source := source) (dying := dying) (content := content) steps)) <+:
      relationJoinConstructionRegionOrigins trace := by
  induction trace with
  | nil =>
      exact ⟨[], by simp [relationJoinConstructionRegionOrigins]⟩
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      rcases induction with ⟨suffix, suffixExact⟩
      refine ⟨suffix.map (prefixRegionOriginLift step) ++
        step.attachment.fragmentRegions.attach.map (fun region =>
          prefixRegionFreshOrigin step
            ⟨region.1, by
              have member := List.mem_filter.mp region.2
              exact of_decide_eq_true member.2⟩), ?_⟩
      simp only [relationJoinConstructionRegionOrigins, List.map_append,
        List.append_assoc]
      rw [← suffixExact]
      simp [List.map_map, prefixRegionOriginLift]

/-- Lookup of a retained source region in the construction enumeration is
independent of how many occurrence-local rows follow it. -/
theorem relationJoinConstructionRegionOrigins_source_get {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (region : source.val.RegionId) :
    (relationJoinConstructionRegionOrigins trace)[region.val]'(by
        have prefixProof :=
          relationJoinConstructionRegionOrigins_source_prefix trace
        have sourceBound : region.val < source.val.regionsList.length := by
          simpa [ConcreteDiagram.regionsList,
            Data.Finite.allFin_eq_finRange] using region.isLt
        exact Nat.lt_of_lt_of_le sourceBound (by
          simpa using prefixProof.length_le)) =
      .inl region := by
  have prefixProof :=
    relationJoinConstructionRegionOrigins_source_prefix trace
  have sourceBound : region.val < source.val.regionsList.length := by
    simpa [ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange] using region.isLt
  have sourceMapBound :
      region.val < (source.val.regionsList.map
        (fun sourceRegion => (Sum.inl sourceRegion :
          RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
            (content := content) steps))).length := by
    simpa using sourceBound
  have row := prefixProof.getElem sourceMapBound
  simpa [ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange] using
    row.symm

theorem relationJoinRawRegionOrigins_nodup
    (result : RelationJoinResult source dying content parameters) :
    (relationJoinRawRegionOrigins result).Nodup := by
  exact relationJoinConstructionRegionOrigins_nodup
    result.construction_trace

theorem relationJoinRawNodeOrigins_nodup
    (result : RelationJoinResult source dying content parameters) :
    (relationJoinRawNodeOrigins result).Nodup := by
  exact (Data.Finite.allFin_nodup _).map _ (by
    intro left right different same
    exact different (rawNodeOriginAt_injective result same))

theorem relationJoinRawWireOrigins_nodup
    (result : RelationJoinResult source dying content parameters) :
    (relationJoinRawWireOrigins result).Nodup := by
  classical
  apply sumEnumerations_nodup
  · exact
      (attach_nodup_of_nodup _
        ((Data.Finite.allFin_nodup _).filter _)).map _ (by
          intro left right different equality
          apply different
          apply Subtype.ext
          exact congrArg
            (fun origin : { wire : source.val.WireId // wire ≠ dying } =>
              origin.1) equality)
  · apply flatMap_nodup_of_disjoint (Data.Finite.allFin_nodup _)
    · intro occurrence _
      exact (attach_nodup_of_nodup _
        ((Data.Finite.allFin_nodup _).filter _)).map _ (by
          intro left right different equality
          apply different
          apply Subtype.ext
          exact congrArg (fun origin => origin.2.1) equality)
    · intro left _ right _ different first firstMember second secondMember equality
      apply different
      have firstOccurrence : first.1 = left := by
        rcases List.mem_map.mp firstMember with ⟨wire, _, rfl⟩
        rfl
      have secondOccurrence : second.1 = right := by
        rcases List.mem_map.mp secondMember with ⟨wire, _, rfl⟩
        rfl
      exact firstOccurrence.symm.trans
        ((congrArg Sigma.fst equality).trans secondOccurrence)

theorem relationJoinRawRegionOrigins_complete
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawRegionOrigin result) :
    origin ∈ relationJoinRawRegionOrigins result := by
  exact relationJoinConstructionRegionOrigins_complete
    result.construction_trace origin

theorem relationJoinRawNodeOrigins_complete
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawNodeOrigin result) :
    origin ∈ relationJoinRawNodeOrigins result := by
  obtain ⟨boundTarget, landing⟩ := prefixNodeLands_total
    result.construction_trace origin.1 origin.2
  let target : result.plainFinal.val.NodeId :=
    Fin.cast result.plainFinal_nodeCount.symm boundTarget
  have targetExact : rawNodeOriginAt result target = origin := by
    apply Subtype.ext
    simpa [rawNodeOriginAt, target] using landing.exact
  apply List.mem_map.mpr
  exact ⟨target, by
    simp [ConcreteDiagram.nodesList, Data.Finite.mem_allFin], targetExact⟩

theorem relationJoinRawWireOrigins_complete
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawWireOrigin result) :
    origin ∈ relationJoinRawWireOrigins result := by
  classical
  rcases origin with ⟨wire, survives⟩ | ⟨occurrence, wire, internal⟩
  · simp [relationJoinRawWireOrigins, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, survives]
  · simp [relationJoinRawWireOrigins,
      ConcreteSpliceAttachment.fragmentInternalWires,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin, internal]

private def relationJoinRawRegionFreshCount
    (steps : List (RelationJoinStep source dying content)) : Nat :=
  (steps.map fun step => step.attachment.fragmentRegions.length).sum

private def relationJoinRawWireFreshCount
    (steps : List (RelationJoinStep source dying content)) : Nat :=
  (steps.map fun step => step.attachment.fragmentInternalWires.length).sum

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

private theorem sum_map_get_allFin (values : List α) (measure : α → Nat) :
    ((Data.Finite.allFin values.length).map
      (fun index => measure (values.get index))).sum =
        (values.map measure).sum := by
  have mapped := congrArg (List.map measure) (map_get_allFin values)
  have summed := congrArg List.sum mapped
  simpa only [List.map_map, Function.comp_apply] using summed

private theorem sum_map_getNat_allFin (values : List α) (measure : α → Nat) :
    ((Data.Finite.allFin values.length).map
      (fun index => measure values[index.1])).sum =
        (values.map measure).sum := by
  simpa only [List.get_eq_getElem] using sum_map_get_allFin values measure

theorem relationJoinSemanticTrace_regionCount_exact
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {regionImage : source.val.RegionId → final.val.RegionId}
    {nodeImage : source.val.NodeId → Option final.val.NodeId}
    {wireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinSemanticTrace source dying content parameters args
      steps final regionImage nodeImage wireImage finalDying finalScope) :
    final.val.regionCount =
      source.val.regionCount + relationJoinRawRegionFreshCount steps := by
  induction trace with
  | nil => simp [relationJoinRawRegionFreshCount]
  | snoc trace step priorExact _ _ _ _ _ _ _ induction =>
      subst priorExact
      have stepCount := step.checked_regionCount
      simp [relationJoinRawRegionFreshCount] at induction ⊢
      omega

theorem relationJoinSemanticTrace_wireCount_exact
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {regionImage : source.val.RegionId → final.val.RegionId}
    {nodeImage : source.val.NodeId → Option final.val.NodeId}
    {wireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinSemanticTrace source dying content parameters args
      steps final regionImage nodeImage wireImage finalDying finalScope) :
    final.val.wireCount =
      source.val.wireCount + relationJoinRawWireFreshCount steps := by
  induction trace with
  | nil => simp [relationJoinRawWireFreshCount]
  | snoc trace step priorExact _ _ _ _ _ _ _ induction =>
      subst priorExact
      have stepCount := step.checked_wireCount
      simp [relationJoinRawWireFreshCount] at induction ⊢
      omega

theorem relationJoinRawRegionOrigins_length
    (result : RelationJoinResult source dying content parameters) :
    result.plainFinal.val.regionCount =
      (relationJoinRawRegionOrigins result).length := by
  rw [result.plainFinal_regionCount]
  exact relationJoinConstructionRegionOrigins_length
    result.construction_trace

theorem relationJoinRawNodeOrigins_length
    (result : RelationJoinResult source dying content parameters) :
    result.plainFinal.val.nodeCount =
      (relationJoinRawNodeOrigins result).length := by
  simp [relationJoinRawNodeOrigins, ConcreteDiagram.nodesList,
    Data.Finite.allFin_eq_finRange]

/-- The terminal node enumeration reads the same authoritative target row as
the executable classifier. -/
theorem relationJoinRawNodeOrigins_get
    (result : RelationJoinResult source dying content parameters)
    (target : result.plainFinal.val.NodeId) :
    (relationJoinRawNodeOrigins result).get
        (Fin.cast (relationJoinRawNodeOrigins_length result) target) =
      rawNodeOriginAt result target := by
  simp [relationJoinRawNodeOrigins, ConcreteDiagram.nodesList,
    Data.Finite.allFin_eq_finRange]

theorem relationJoinRawWireOrigins_length
    (result : RelationJoinResult source dying content parameters) :
    result.plainFinal.val.wireCount =
      (relationJoinRawWireOrigins result).length := by
  have traceCount :=
    relationJoinSemanticTrace_wireCount_exact result.semantic_trace
  have retainedCount :=
    Data.Finite.filter_not_mem_length_add_removed_length
      [dying] (by simp)
  have finalCount := result.plainFinal_wireCount_add_one
  simp [decide_not, Data.Finite.allFin_eq_finRange] at retainedCount
  simp [relationJoinRawWireFreshCount] at traceCount
  simp [relationJoinRawWireOrigins,
    ConcreteDiagram.wiresList] at ⊢
  rw [sum_map_getNat_allFin result.steps
    (fun step => step.attachment.fragmentInternalWires.length)]
  simp [Data.Finite.allFin_eq_finRange] at ⊢
  change result.plainFinal.val.wireCount =
    (List.filter (fun value => !decide (value = dying))
      (List.finRange source.val.wireCount)).length +
        (result.steps.map fun step =>
          step.attachment.fragmentInternalWires.length).sum
  have retainedCount' :
      (List.filter (fun value => !decide (value = dying))
        (List.finRange source.val.wireCount)).length + 1 =
          source.val.wireCount := by
    simpa only using retainedCount
  clear retainedCount
  omega

/-- Executable equivalence from dense positions to a complete nodup
enumeration.  Proof fields justify lookup but do not select runtime data. -/
private def finiteEquivOfEnumeration [DecidableEq α]
    (values : List α)
    (nodup : values.Nodup)
    (complete : ∀ value, value ∈ values) :
    Data.Finite.FiniteEquiv (Fin values.length) α where
  toFun := values.get
  invFun := fun value =>
    (Data.Finite.indexOf? values value).get (by
      rw [Data.Finite.indexOf?_isSome_iff]
      exact complete value)
  left_inv := by
    intro position
    let foundSome :
        (Data.Finite.indexOf? values (values.get position)).isSome = true :=
      Data.Finite.indexOf?_isSome_iff.mpr (List.get_mem values position)
    exact Option.get_of_eq_some foundSome
      (Data.Finite.indexOf?_get_eq_some_of_nodup nodup position)
  right_inv := by
    intro value
    let found := Data.Finite.indexOf? values value
    have foundSome : found.isSome = true := by
      rw [Data.Finite.indexOf?_isSome_iff]
      exact complete value
    obtain ⟨position, positionExact⟩ :=
      Option.isSome_iff_exists.mp foundSome
    rw [Option.get_of_eq_some foundSome positionExact]
    exact Data.Finite.indexOf?_sound positionExact

/-- Direct final-node equivalence.  Its forward map is the sole target-led
ledger read; its inverse computes the landing supplied by structural
construction totality. -/
def relationJoinRawNodeEquiv
    (result : RelationJoinResult source dying content parameters) :
    Data.Finite.FiniteEquiv result.plainFinal.val.NodeId
      (RelationJoinRawNodeOrigin result) where
  toFun := rawNodeOriginAt result
  invFun := fun origin =>
    let landing := prefixNodeLands_total result.construction_trace
      origin.1 origin.2
    Fin.cast result.plainFinal_nodeCount.symm landing.1
  left_inv := by
    intro target
    let landing := prefixNodeLands_total result.construction_trace
      (rawNodeOriginAt result target).1
      (rawNodeOriginAt result target).2
    change Fin.cast result.plainFinal_nodeCount.symm landing.1 = target
    have boundExact := prefixNodeLands_functional
      landing.2 (rawNodeOriginAt_lands result target)
    apply Fin.ext
    simpa using congrArg Fin.val boundExact
  right_inv := by
    intro origin
    let landing := prefixNodeLands_total result.construction_trace
      origin.1 origin.2
    change rawNodeOriginAt result
      (Fin.cast result.plainFinal_nodeCount.symm landing.1) = origin
    apply Subtype.ext
    simpa [rawNodeOriginAt, landing] using landing.2.exact

/-- Constructive, allocation-neutral classifiers for every final raw carrier.
The inverse maps recover the dense raw identifier assigned to each origin. -/
structure RelationJoinRawOriginAtlas
    (result : RelationJoinResult source dying content parameters) where
  regionEquiv : Data.Finite.FiniteEquiv result.plainFinal.val.RegionId
    (RelationJoinRawRegionOrigin result)
  nodeEquiv : Data.Finite.FiniteEquiv result.plainFinal.val.NodeId
    (RelationJoinRawNodeOrigin result)
  wireEquiv : Data.Finite.FiniteEquiv result.plainFinal.val.WireId
    (RelationJoinRawWireOrigin result)

namespace RelationJoinRawOriginAtlas

/-- Compute all three raw-origin classifiers from the semantic receipt. -/
def ofResult
    (result : RelationJoinResult source dying content parameters) :
    RelationJoinRawOriginAtlas result where
  regionEquiv :=
    (Data.Finite.FiniteEquiv.finCast
      (relationJoinRawRegionOrigins_length result)).trans
        (finiteEquivOfEnumeration
          (relationJoinRawRegionOrigins result)
          (relationJoinRawRegionOrigins_nodup result)
          (relationJoinRawRegionOrigins_complete result))
  nodeEquiv :=
    relationJoinRawNodeEquiv result
  wireEquiv :=
    (Data.Finite.FiniteEquiv.finCast
      (relationJoinRawWireOrigins_length result)).trans
        (finiteEquivOfEnumeration
          (relationJoinRawWireOrigins result)
          (relationJoinRawWireOrigins_nodup result)
          (relationJoinRawWireOrigins_complete result))

/-- Classify a raw final region by allocation-neutral origin. -/
def regionOrigin (atlas : RelationJoinRawOriginAtlas result)
    (region : result.plainFinal.val.RegionId) :
    RelationJoinRawRegionOrigin result :=
  atlas.regionEquiv region

/-- Classify a raw final node by allocation-neutral origin. -/
def nodeOrigin (atlas : RelationJoinRawOriginAtlas result)
    (node : result.plainFinal.val.NodeId) :
    RelationJoinRawNodeOrigin result :=
  atlas.nodeEquiv node

/-- Classify a raw final wire by allocation-neutral origin. -/
def wireOrigin (atlas : RelationJoinRawOriginAtlas result)
    (wire : result.plainFinal.val.WireId) :
    RelationJoinRawWireOrigin result :=
  atlas.wireEquiv wire

/-- The executable final-node atlas is definitionally the sole target-led
construction-ledger classifier. -/
theorem ofResult_node_exact
    (result : RelationJoinResult source dying content parameters)
    (target : result.plainFinal.val.NodeId) :
    (ofResult result).nodeEquiv target = rawNodeOriginAt result target :=
  rfl

/-- Any exact construction landing identifies the corresponding terminal
atlas row, after the node-preserving final wire deletion. -/
theorem ofResult_node_exact_of_landing
    (result : RelationJoinResult source dying content parameters)
    {origin : RelationJoinRawNodeOrigin result}
    {target : result.boundFinal.val.NodeId}
    (landing : PrefixNodeLands result.construction_trace origin.1 target) :
    (ofResult result).nodeEquiv
        (Fin.cast result.plainFinal_nodeCount.symm target) = origin := by
  apply Subtype.ext
  simpa [ofResult, relationJoinRawNodeEquiv, rawNodeOriginAt] using
    landing.exact

/-- Allocation-neutral region payload. -/
inductive RelationJoinRawRegionData (Region : Type)
  | sheet
  | cut (parent : Region)
  deriving Repr, DecidableEq

/-- Allocation-neutral node payload. -/
inductive RelationJoinRawNodeData (Region : Type) (definitionCount : Nat)
  | atom (region : Region) (args : List Sig)
  | ref (region : Region) (definition : Fin definitionCount)
      (args : List Sig)
  | identity (region : Region) (sig : Sig) (arity : Nat)
  deriving Repr, DecidableEq

/-- Allocation-neutral incidence endpoint. -/
structure RelationJoinRawEndpoint (Node : Type) where
  node : Node
  port : CPort
  deriving Repr, DecidableEq

/-- Allocation-neutral wire payload, including its authoritative ordered
endpoint fiber. -/
structure RelationJoinRawWireData (Region Node : Type) where
  sig : Sig
  scope : Region
  endpoints : List (RelationJoinRawEndpoint Node)
  deriving Repr, DecidableEq

/-- A content region lands at the occurrence's source site when it is the
fragment root, and otherwise retains its occurrence-local origin. -/
def contentRegionOrigin
    (result : RelationJoinResult source dying content parameters)
    (occurrence : Fin result.steps.length)
    (region : content.val.diagram.RegionId) :
    RelationJoinRawRegionOrigin result :=
  if root : region = content.val.diagram.root then
    .inl (result.steps.get occurrence).sourceRegion
  else
    .inr ⟨occurrence, ⟨region, root⟩⟩

/-- Authoritative raw region row derived only from source/content tables and
the occurrence's checked splice site. -/
def expectedRegionData
    (result : RelationJoinResult source dying content parameters) :
    RelationJoinRawRegionOrigin result →
      RelationJoinRawRegionData (RelationJoinRawRegionOrigin result)
  | .inl region =>
      match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (.inl parent)
  | .inr ⟨occurrence, region⟩ =>
      match content.val.diagram.regions region.1 with
      | .sheet => .sheet
      | .cut parent => .cut (contentRegionOrigin result occurrence parent)

/-- Authoritative raw node row derived only from retained source nodes,
occurrence content, and the attachment's generated request list. -/
def expectedNodeData
    (result : RelationJoinResult source dying content parameters) :
    RelationJoinRawNodeOrigin result →
      RelationJoinRawNodeData (RelationJoinRawRegionOrigin result)
        definitions.length
  | ⟨.inl node, _⟩ =>
      match source.val.nodes node with
      | .atom region args => .atom (.inl region) args
      | .ref region definition args => .ref (.inl region) definition args
      | .identity region sig arity => .identity (.inl region) sig arity
  | ⟨.inr ⟨occurrence, .inl node⟩, _⟩ =>
      match content.val.diagram.nodes node with
      | .atom region args =>
          .atom (contentRegionOrigin result occurrence region) args
      | .ref region definition args =>
          .ref (contentRegionOrigin result occurrence region) definition args
      | .identity region sig arity =>
          .identity (contentRegionOrigin result occurrence region) sig arity
  | ⟨.inr ⟨occurrence, .inr request⟩, _⟩ =>
      let step := result.steps.get occurrence
      let requestData := step.attachment.identityRequests.get request
      .identity (.inl step.sourceRegion) requestData.sig
        requestData.attachments.length

/-- The signature of a raw wire origin is inherited from exactly one source
or occurrence-internal content wire. -/
def expectedWireSignature
    (result : RelationJoinResult source dying content parameters) :
    RelationJoinRawWireOrigin result → Sig
  | .inl wire => (source.val.wires wire.1).sig
  | .inr ⟨_occurrence, wire⟩ =>
      (content.val.diagram.wires wire.1).sig

/-- The scope of a raw wire origin is inherited from its source region or
mapped through the occurrence's root-identifying region construction. -/
def expectedWireScope
    (result : RelationJoinResult source dying content parameters) :
    RelationJoinRawWireOrigin result → RelationJoinRawRegionOrigin result
  | .inl wire => .inl (source.val.wires wire.1).scope
  | .inr ⟨occurrence, wire⟩ =>
      contentRegionOrigin result occurrence
        (content.val.diagram.wires wire.1).scope

/-- Destination origin of one content wire at a checked occurrence.  Boundary
wires use the first positional representative selected by the attachment;
internal wires retain an occurrence-local origin. -/
def contentWireOrigin
    (result : RelationJoinResult source dying content parameters)
    (occurrence : Fin result.steps.length)
    (wire : content.val.diagram.WireId) :
    RelationJoinRawWireOrigin result :=
  let step := result.steps.get occurrence
  if boundary : wire ∈ content.val.boundary then
    let position := step.attachment.representativePosition wire boundary
    let sourcePosition : Fin step.sourceAttachments.length :=
      Fin.cast step.sourceAttachmentArity.symm position
    .inl
      ⟨step.sourceAttachments.get sourcePosition,
        step.sourceAttachmentsSurvive sourcePosition⟩
  else
    .inr ⟨occurrence, ⟨wire, boundary⟩⟩

/-- Retained source incidence before any generated occurrence incidence is
appended.  Consumed application endpoints and the exhausted relation wire
are removed by the same construction predicates used by the join. -/
def expectedSourceEndpointOccurrences
    (result : RelationJoinResult source dying content parameters) :
    List
      (RelationJoinRawWireOrigin result ×
        RelationJoinRawEndpoint (RelationJoinRawNodeOrigin result)) :=
  source.val.endpointOccurrences.filterMap fun occurrence =>
    if nodeSurvives : occurrence.2.node ∉ result.applications then
      if wireSurvives : occurrence.1 ≠ dying then
        some
          (.inl ⟨occurrence.1, wireSurvives⟩,
            { node := ⟨.inl occurrence.2.node, by
                simpa [RelationJoinPrefixNodeLive,
                  result.steps_application_order] using nodeSurvives⟩
              port := occurrence.2.port })
      else none
    else none

/-- Copied content incidence contributed by one occurrence, in the content
diagram's authoritative wire/endpoint order. -/
def expectedFragmentEndpointOccurrences
    (result : RelationJoinResult source dying content parameters)
    (occurrence : Fin result.steps.length) :
    List
      (RelationJoinRawWireOrigin result ×
        RelationJoinRawEndpoint (RelationJoinRawNodeOrigin result)) :=
  content.val.diagram.endpointOccurrences.map fun endpointOccurrence =>
    (contentWireOrigin result occurrence endpointOccurrence.1,
      { node := ⟨.inr ⟨occurrence, .inl endpointOccurrence.2.node⟩,
          trivial⟩
        port := endpointOccurrence.2.port })

/-- Equality-node incidence contributed by repeated boundary aliases at one
occurrence, in request order and then attachment-port order. -/
def expectedIdentityEndpointOccurrences
    (result : RelationJoinResult source dying content parameters)
    (occurrence : Fin result.steps.length) :
    List
      (RelationJoinRawWireOrigin result ×
        RelationJoinRawEndpoint (RelationJoinRawNodeOrigin result)) :=
  let step := result.steps.get occurrence
  (Data.Finite.allFin step.attachment.identityRequests.length).flatMap
    fun request =>
      let requestData := step.attachment.identityRequests.get request
      (Data.Finite.allFin requestData.attachments.length).map fun port =>
        (.inl
            ⟨step.identityRequestSourceWire request port,
              step.identityRequestSourceWire_survives request port⟩,
          { node := ⟨.inr ⟨occurrence, .inr request⟩, trivial⟩
            port := .identity port.val })

/-- Complete construction-order incidence stream.  This is the independent
wire-endpoint fold: retained source incidence first, followed by each splice's
fragment incidences and request incidences. -/
def expectedEndpointOccurrences
    (result : RelationJoinResult source dying content parameters) :
    List
      (RelationJoinRawWireOrigin result ×
        RelationJoinRawEndpoint (RelationJoinRawNodeOrigin result)) :=
  expectedSourceEndpointOccurrences result ++
    (Data.Finite.allFin result.steps.length).flatMap fun occurrence =>
      expectedFragmentEndpointOccurrences result occurrence ++
        expectedIdentityEndpointOccurrences result occurrence

/-- Authoritative ordered endpoint fiber of one raw wire origin. -/
def expectedWireEndpoints
    (result : RelationJoinResult source dying content parameters)
    (wire : RelationJoinRawWireOrigin result) :
    List (RelationJoinRawEndpoint (RelationJoinRawNodeOrigin result)) :=
  (expectedEndpointOccurrences result).filterMap fun occurrence =>
    if occurrence.1 = wire then some occurrence.2 else none

/-- Complete authoritative raw wire row. -/
def expectedWireData
    (result : RelationJoinResult source dying content parameters)
    (wire : RelationJoinRawWireOrigin result) :
    RelationJoinRawWireData (RelationJoinRawRegionOrigin result)
      (RelationJoinRawNodeOrigin result) :=
  { sig := expectedWireSignature result wire
    scope := expectedWireScope result wire
    endpoints := expectedWireEndpoints result wire }

/-- Final-to-neutral endpoint carrier induced solely by the atlas's node
origin equivalence; ports are preserved verbatim. -/
def endpointOriginEquiv
    (atlas : RelationJoinRawOriginAtlas result) :
    Data.Finite.FiniteEquiv
      (CEndpoint result.plainFinal.val.nodeCount)
      (RelationJoinRawEndpoint (RelationJoinRawNodeOrigin result)) where
  toFun := fun endpoint =>
    { node := atlas.nodeEquiv endpoint.node
      port := endpoint.port }
  invFun := fun endpoint =>
    { node := atlas.nodeEquiv.symm endpoint.node
      port := endpoint.port }
  left_inv := by
    intro endpoint
    cases endpoint with
    | mk node port =>
        congr
        exact atlas.nodeEquiv.left_inv node
  right_inv := by
    intro endpoint
    cases endpoint with
    | mk node port =>
        congr
        exact atlas.nodeEquiv.right_inv node

/-- Construction-derived reverse incidence at one node origin.  Positions
and repeated incidences are retained because this filters the authoritative
forward occurrence stream rather than deduplicating it. -/
def expectedReverseIncidence
    (result : RelationJoinResult source dying content parameters)
    (node : RelationJoinRawNodeOrigin result) :
    List (RelationJoinRawWireOrigin result × CPort) :=
  (expectedEndpointOccurrences result).filterMap fun occurrence =>
    if occurrence.2.node = node then
      some (occurrence.1, occurrence.2.port)
    else none

theorem mem_expectedReverseIncidence
    (result : RelationJoinResult source dying content parameters)
    (node : RelationJoinRawNodeOrigin result)
    (wire : RelationJoinRawWireOrigin result)
    (port : CPort) :
    (wire, port) ∈ expectedReverseIncidence result node ↔
      (wire, { node := node, port := port }) ∈
        expectedEndpointOccurrences result := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨occurrence, occurrenceMember, emitted⟩
    split at emitted
    · rename_i nodeExact
      have exact := Option.some.inj emitted
      cases occurrence with
      | mk occurrenceWire endpoint =>
          simp only at exact
          cases exact
          cases endpoint with
          | mk endpointNode endpointPort =>
              have nodeExact' : endpointNode = node := nodeExact
              cases nodeExact'
              exact occurrenceMember
    · cases emitted
  · intro member
    apply List.mem_filterMap.mpr
    refine ⟨(wire, { node := node, port := port }), member, ?_⟩
    simp

/-- The raw root remains the retained source root. -/
def expectedRoot
    (result : RelationJoinResult source dying content parameters) :
    RelationJoinRawRegionOrigin result :=
  .inl source.val.root

/-- The executable atlas classifier agrees with every construction-derived
plain-final region landing. -/
theorem ofResult_region_exact_of_landing
    (result : RelationJoinResult source dying content parameters)
    {origin : RelationJoinRawRegionOrigin result}
    {target : result.plainFinal.val.RegionId}
    (landing : plainPrefixRegionLands result origin target) :
    (ofResult result).regionEquiv target = origin := by
  rcases landing with ⟨bound, boundLanding, rfl⟩
  unfold ofResult finiteEquivOfEnumeration
  change (relationJoinRawRegionOrigins result).get
      (Fin.cast (relationJoinRawRegionOrigins_length result)
        (result.plainBoundRegionImage bound)) = origin
  have row := relationJoinConstructionRegionOrigins_landing_exact
    boundLanding
  simpa [relationJoinRawRegionOrigins] using row

/-- The inverse atlas row is exactly the unique construction-derived landing
of that neutral region origin. -/
theorem ofResult_region_inverse_lands
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawRegionOrigin result) :
    plainPrefixRegionLands result origin
      ((ofResult result).regionEquiv.symm origin) := by
  obtain ⟨target, landing⟩ := plainPrefixRegionLands_total result origin
  have inverseExact : (ofResult result).regionEquiv.symm origin = target := by
    apply (ofResult result).regionEquiv.injective
    rw [(ofResult result).regionEquiv.apply_symm_apply,
      ofResult_region_exact_of_landing result landing]
  rw [inverseExact]
  exact landing

/-- The executable enumeration classifier sends every retained source region
to its source origin. -/
theorem ofResult_source_region_exact
    (result : RelationJoinResult source dying content parameters)
    (region : source.val.RegionId) :
    (ofResult result).regionEquiv
        (result.plainBoundRegionImage
          (result.boundRegionImage region)) = .inl region := by
  unfold ofResult finiteEquivOfEnumeration
  change (relationJoinRawRegionOrigins result).get
      (Fin.cast (relationJoinRawRegionOrigins_length result)
        (result.plainBoundRegionImage
          (result.boundRegionImage region))) = .inl region
  have sourceRow := relationJoinConstructionRegionOrigins_source_get
    result.construction_trace region
  simpa [relationJoinRawRegionOrigins] using sourceRow

theorem ofResult_root_exact
    (result : RelationJoinResult source dying content parameters) :
    (ofResult result).regionEquiv result.plainFinal.val.root =
      expectedRoot result := by
  rw [result.plainFinal_root_eq_source_image]
  have landing := ofResult_source_region_exact result source.val.root
  simpa [expectedRoot] using landing

theorem ofResult_source_region_data_exact
    (result : RelationJoinResult source dying content parameters)
    (region : source.val.RegionId) :
    (match result.plainFinal.val.regions
        ((ofResult result).regionEquiv.symm (.inl region)) with
      | .sheet => RelationJoinRawRegionData.sheet
      | .cut parent =>
          RelationJoinRawRegionData.cut
            ((ofResult result).regionEquiv parent)) =
      expectedRegionData result (.inl region) := by
  let actual := result.plainBoundRegionImage
    (result.boundRegionImage region)
  have landing : (ofResult result).regionEquiv actual = .inl region :=
    ofResult_source_region_exact result region
  have inverseExact :
      (ofResult result).regionEquiv.symm (.inl region) = actual := by
    apply (ofResult result).regionEquiv.injective
    rw [(ofResult result).regionEquiv.apply_symm_apply, landing]
  rw [inverseExact]
  rw [result.plainSourceRegionImage_data]
  cases data : source.val.regions region with
  | sheet => simp [expectedRegionData, data]
  | cut parent =>
      simp only [expectedRegionData, data]
      exact congrArg RelationJoinRawRegionData.cut
        (ofResult_source_region_exact result parent)

/-- Exact table obligations connecting the allocation-neutral expected model
to the checked raw construction.  The right-hand sides are the independent
source/content/request fold above; no final-table readback participates in
their definition. -/
structure Conformance
    (atlas : RelationJoinRawOriginAtlas result) : Prop where
  root_exact :
    atlas.regionEquiv result.plainFinal.val.root =
      expectedRoot result
  region_exact : ∀ origin,
    (match result.plainFinal.val.regions (atlas.regionEquiv.symm origin) with
      | .sheet => RelationJoinRawRegionData.sheet
      | .cut parent =>
          RelationJoinRawRegionData.cut (atlas.regionEquiv parent)) =
      expectedRegionData result origin
  node_exact : ∀ origin,
    (match result.plainFinal.val.nodes (atlas.nodeEquiv.symm origin) with
      | .atom region args =>
          RelationJoinRawNodeData.atom (atlas.regionEquiv region) args
      | .ref region definition args =>
          RelationJoinRawNodeData.ref (atlas.regionEquiv region)
            definition args
      | .identity region sig arity =>
          RelationJoinRawNodeData.identity (atlas.regionEquiv region)
            sig arity) = expectedNodeData result origin
  wire_signature_exact : ∀ origin,
    (result.plainFinal.val.wires (atlas.wireEquiv.symm origin)).sig =
      expectedWireSignature result origin
  wire_scope_exact : ∀ origin,
    atlas.regionEquiv
        (result.plainFinal.val.wires
          (atlas.wireEquiv.symm origin)).scope =
      expectedWireScope result origin
  wire_endpoints_exact : ∀ origin,
    (result.plainFinal.val.wires
        (atlas.wireEquiv.symm origin)).endpoints.map
          atlas.endpointOriginEquiv =
      expectedWireEndpoints result origin

/-- Bidirectional endpoint fiber over one independently specified wire row. -/
structure EndpointFiberEquiv
    (atlas : RelationJoinRawOriginAtlas result)
    (wire : RelationJoinRawWireOrigin result) where
  equivalence :
    Data.Finite.FiniteEquiv
      { endpoint // endpoint ∈
        (result.plainFinal.val.wires
          (atlas.wireEquiv.symm wire)).endpoints }
      { endpoint // endpoint ∈ expectedWireEndpoints result wire }
  forward_exact : ∀ endpoint,
    (equivalence endpoint).1 = atlas.endpointOriginEquiv endpoint.1
  inverse_exact : ∀ endpoint,
    (equivalence.symm endpoint).1 =
      atlas.endpointOriginEquiv.symm endpoint.1

/-- Restrict the construction-owned endpoint carrier equivalence to one wire
fiber using the proved ordered endpoint equation. -/
def endpointFiberEquiv
    (atlas : RelationJoinRawOriginAtlas result)
    (conformance : Conformance atlas)
    (wire : RelationJoinRawWireOrigin result) :
    EndpointFiberEquiv atlas wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨atlas.endpointOriginEquiv endpoint.1, by
          rw [← conformance.wire_endpoints_exact wire]
          exact List.mem_map.mpr ⟨endpoint.1, endpoint.2, rfl⟩⟩
      invFun := fun endpoint =>
        ⟨atlas.endpointOriginEquiv.symm endpoint.1, by
          have mappedMember : endpoint.1 ∈
              (result.plainFinal.val.wires
                (atlas.wireEquiv.symm wire)).endpoints.map
                  atlas.endpointOriginEquiv := by
            rw [conformance.wire_endpoints_exact wire]
            exact endpoint.2
          rcases List.mem_map.mp mappedMember with
            ⟨rawEndpoint, rawMember, exact⟩
          have rawExact : rawEndpoint =
              atlas.endpointOriginEquiv.symm endpoint.1 := by
            apply atlas.endpointOriginEquiv.injective
            rw [atlas.endpointOriginEquiv.apply_symm_apply]
            exact exact
          simpa only [rawExact] using rawMember⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact atlas.endpointOriginEquiv.left_inv endpoint.1
      right_inv := by
        intro endpoint
        apply Subtype.ext
        exact atlas.endpointOriginEquiv.right_inv endpoint.1 }
  forward_exact := by intro; rfl
  inverse_exact := by intro; rfl

end RelationJoinRawOriginAtlas

end Origins

end MonolithicWireQuantifier

end VisualProof
