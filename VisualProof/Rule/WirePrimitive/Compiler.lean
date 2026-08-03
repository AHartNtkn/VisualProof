import VisualProof.Rule.WirePrimitive.CompilerTermination
import VisualProof.Rule.WirePrimitive.ArgumentsDropTransport
import VisualProof.Rule.WirePrimitive.ArgumentsExtendTransport
import VisualProof.Rule.WirePrimitive.ArgumentsArityTransport
import VisualProof.Rule.WirePrimitive.ArgumentsDuplicateTransport
import VisualProof.Rule.MonolithicWireQuantifierRaw
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawEndpointTerminalConformance
import VisualProof.Diagram.Concrete.IsomorphismSearch

namespace VisualProof

namespace WirePrimitive

/-- Stable authoring-layer compiler failures. -/
inductive CompilerError
  | monolithicJoinRejected (error : MonolithicWireQuantifierError)
  | monolithicSeverRejected (error : MonolithicWireQuantifierError)
  | malformedResidual
  | missingAmbient
  | trackedWireConsumed
  | allocationMismatch
  | contentRejected (error : Content.WireContentError)
  | argumentRejected (error : Arguments.WireArgumentError)
  | leafRejected (error : Leaves.WireLeafError)
  | partitionRejected (error : Partition.WirePartitionError)
  | vacuousRejected (error : StructuralCore.VacuousError)
  | redundancyMismatch
  deriving Repr, DecidableEq

private def requireOption
    (error : CompilerError) : Option α → Except CompilerError α
  | none => .error error
  | some value => .ok value

private theorem length_filter_true (values : List α) :
    (values.filter fun _ => true).length = values.length := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [induction]

@[simp]
private theorem cast_list_length
    {source target : Type}
    (exact : source = target)
    (values : List source) :
    (cast (congrArg List exact) values).length = values.length := by
  subst exact
  rfl

private def castWireList
    {left right : CheckedDiagram definitions}
    (exact : left = right)
    (values : List left.val.WireId) :
    List right.val.WireId :=
  exact ▸ values

@[simp]
private theorem castWireList_length
    {left right : CheckedDiagram definitions}
    (exact : left = right)
    (values : List left.val.WireId) :
    (castWireList exact values).length = values.length := by
  subst exact
  rfl

private def checkedDiagramEqIso
    {left right : CheckedDiagram definitions}
    (exact : left = right) : ConcreteIso left.val right.val := by
  subst right
  exact Vacuity.identityIso left.val left.property

/--
Exact ordered boundary validation for one accepted join input.  Lists are not
deduplicated, so repeated and permuted formal positions remain observable.
-/
structure JoinBoundaryReceipt
    {source : CheckedDiagram definitions}
    (input : MonolithicRelationJoinInput source)
    (arguments : List Sig) where
  private marker : Unit
  boundaryLength :
    input.content.val.boundary.length =
      arguments.length + input.parameters.length
  formalSignatures :
    (input.content.val.boundary.take arguments.length).map
        (fun wire => (input.content.val.diagram.wires wire).sig) =
      arguments
  parameterSignatures :
    (input.content.val.boundary.drop arguments.length).map
        (fun wire => (input.content.val.diagram.wires wire).sig) =
      input.parameters.map (fun wire => (source.val.wires wire).sig)

/--
The proof-carrying initial obligation for every accepted strongest join.
Unlike the executable comparison compiler below, this construction has no
failure case: the monolithic checker already owns the exact open compilation,
applied-site, ordered-boundary, and non-aliasing evidence.
-/
def initialIntrinsicResidual
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (monolithic : AcceptedMonolithicRelationJoin source input) :
    IntrinsicCompilerResidual source
      (ConcreteElaboration.openBoundaryClassSigs input.content.val) :=
  IntrinsicCompilerResidual.initial monolithic.contentCompilation
    input.wire monolithic.arguments monolithic.sourceSignature
    monolithic.sourceSites input.parameters
    (by simpa [checkedBoundarySigs] using monolithic.formalSignatures)
    (by simpa [checkedBoundarySigs] using monolithic.parameterSignatures)
    monolithic.live_not_parameter

/-- The primitive compiler and raw splice trace enumerate the same accepted
applications, although the former follows dying-wire endpoint order and the
latter follows dense source-node order. -/
private theorem sourceSiteNodes_perm_applications
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : ConcreteWireQuantifier.RelationJoinResult source wire content
      parameters)
    (sites : AllAppliedSites source wire) :
    (sites.sites.map AppliedSite.node).Perm result.applications := by
  have siteNodesNodup :
      (sites.sites.map AppliedSite.node).Nodup := by
    have nodeNodupOfEndpointNodup :
        ∀ values : List (AppliedSite source wire),
          (values.map AppliedSite.endpoint).Nodup →
            (values.map AppliedSite.node).Nodup := by
      intro values
      induction values with
    | nil => simp
      | cons head tail induction =>
          intro endpointNodup
          rw [List.map_cons, List.nodup_cons] at endpointNodup
          rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, induction endpointNodup.2⟩
          intro member
          rcases List.mem_map.mp member with
            ⟨candidate, candidateMember, same⟩
          apply endpointNodup.1
          apply List.mem_map.mpr
          refine ⟨candidate, candidateMember, ?_⟩
          exact congrArg
            (fun node : source.val.NodeId =>
              (⟨node, .head⟩ : CEndpoint source.val.nodeCount))
            same
    exact nodeNodupOfEndpointNodup sites.sites sites.endpoints_nodup
  have applicationNodesNodup : result.applications.Nodup := by
    rw [result.applications_storage_order]
    exact (Data.Finite.allFin_nodup _).filter _
  apply Data.Finite.list_perm_of_nodup_mem_iff siteNodesNodup
    applicationNodesNodup
  intro node
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨site, siteMember, rfl⟩
    rw [result.applications_storage_order]
    apply List.mem_filter.mpr
    refine ⟨Data.Finite.mem_allFin site.node, ?_⟩
    apply decide_eq_true
    rw [← sites.exhaustive]
    exact List.mem_map.mpr ⟨site, siteMember, rfl⟩
  · intro member
    rw [result.applications_storage_order] at member
    have endpointMember :
        (⟨node, .head⟩ : CEndpoint source.val.nodeCount) ∈
          (source.val.wires wire).endpoints :=
      of_decide_eq_true (List.mem_filter.mp member).2
    rw [← sites.exhaustive] at endpointMember
    rcases List.mem_map.mp endpointMember with
      ⟨site, siteMember, endpointExact⟩
    exact List.mem_map.mpr
      ⟨site, siteMember, congrArg CEndpoint.node endpointExact⟩

/-- Construction-owned conversion from primitive site positions to raw splice
positions.  Equal nodes are matched directly; no graph isomorphism is searched
for. -/
private def sourceSiteStepPositions
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : ConcreteWireQuantifier.RelationJoinResult source wire content
      parameters)
    (sites : AllAppliedSites source wire) :
    { equivalence : Data.Finite.FiniteEquiv
        (Fin sites.sites.length) (Fin result.steps.length) //
      ∀ position,
        (result.steps.get (equivalence position)).application =
            (sites.sites.get position).node ∧
          (result.steps.get (equivalence position)).sourceRegion =
            (sites.sites.get position).region } := by
  let siteNodes := sites.sites.map AppliedSite.node
  let stepNodes := result.steps.map
    ConcreteWireQuantifier.RelationJoinStep.application
  have permuted : siteNodes.Perm stepNodes :=
    (sourceSiteNodes_perm_applications result sites).trans
      (List.Perm.of_eq result.steps_application_order.symm)
  let positions := Data.Finite.FiniteEquiv.ofListPermStable permuted
  have siteLength : siteNodes.length = sites.sites.length := by
    simp [siteNodes]
  have stepLength : stepNodes.length = result.steps.length := by
    simp [stepNodes]
  let siteCast := Data.Finite.FiniteEquiv.finCast
    siteLength.symm
  let stepCast := Data.Finite.FiniteEquiv.finCast stepLength
  refine ⟨siteCast.trans (positions.1.trans stepCast), ?_⟩
  intro position
  have exact := positions.2 (siteCast position)
  have applicationExact :
      (result.steps.get
          (siteCast.trans (positions.1.trans stepCast) position)).application =
        (sites.sites.get position).node := by
    simpa [siteNodes, stepNodes, siteCast, stepCast,
      Data.Finite.FiniteEquiv.finCast, List.get_eq_getElem,
      List.getElem_map] using exact
  refine ⟨applicationExact, ?_⟩
  have nodeData :=
    (result.steps.get
      (siteCast.trans (positions.1.trans stepCast) position)).sourceNodeExact
  rw [applicationExact] at nodeData
  exact (CNode.atom.inj
    (nodeData.symm.trans (sites.sites.get position).node_data)).1

/-- Rebuild the raw recursive construction-wire origin named by one accepted
occurrence and its checked local internal-wire position.  This is the inverse
direction missing from `constructionWireDescriptor`; the compiler uses it to
land each primitive-created internal wire directly in the raw terminal wire
carrier. -/
private def constructionWireOriginAt :
    (steps : List (ConcreteWireQuantifier.RelationJoinStep source dying
      content)) →
    (occurrence : Fin steps.length) →
    Fin ((steps.get occurrence).attachment.fragmentInternalWires.length) →
      ConcreteWireQuantifier.ConstructionWireOrigin steps
  | [], occurrence, _ => nomatch occurrence
  | step :: rest, ⟨0, _⟩, position =>
      .head (by simpa using position)
  | step :: rest, ⟨index + 1, bound⟩, position =>
      .tail (constructionWireOriginAt rest
        ⟨index, Nat.lt_of_succ_lt_succ bound⟩ (by simpa using position))

@[simp]
private theorem constructionWireDescriptor_originAt_occurrence
    (steps : List (ConcreteWireQuantifier.RelationJoinStep source dying
      content))
    (occurrence : Fin steps.length)
    (position : Fin
      ((steps.get occurrence).attachment.fragmentInternalWires.length)) :
    (ConcreteWireQuantifier.constructionWireDescriptor
      (constructionWireOriginAt steps occurrence position)).occurrence =
        occurrence := by
  induction steps with
  | nil => exact Fin.elim0 occurrence
  | cons step rest induction =>
      rcases occurrence with ⟨_ | index, bound⟩
      · rfl
      · simp only [constructionWireOriginAt,
          ConcreteWireQuantifier.constructionWireDescriptor]
        have tailExact := induction
          ⟨index, Nat.lt_of_succ_lt_succ bound⟩ (by simpa using position)
        apply Fin.ext
        simpa using congrArg Fin.val tailExact

@[simp]
private theorem constructionWireDescriptor_originAt_position
    (steps : List (ConcreteWireQuantifier.RelationJoinStep source dying
      content))
    (occurrence : Fin steps.length)
    (position : Fin
      ((steps.get occurrence).attachment.fragmentInternalWires.length)) :
    (ConcreteWireQuantifier.constructionWireDescriptor
      (constructionWireOriginAt steps occurrence position)).position.val =
        position.val := by
  induction steps with
  | nil => exact Fin.elim0 occurrence
  | cons step rest induction =>
      rcases occurrence with ⟨_ | index, bound⟩
      · rfl
      · simp only [constructionWireOriginAt,
          ConcreteWireQuantifier.constructionWireDescriptor]
        simpa using induction
          ⟨index, Nat.lt_of_succ_lt_succ bound⟩ (by simpa using position)

@[simp]
private theorem constructionWireOriginAt_descriptor
    {steps : List (ConcreteWireQuantifier.RelationJoinStep source dying
      content)}
    (origin : ConcreteWireQuantifier.ConstructionWireOrigin steps) :
    constructionWireOriginAt steps
        (ConcreteWireQuantifier.constructionWireDescriptor origin).occurrence
        (ConcreteWireQuantifier.constructionWireDescriptor origin).position =
      origin := by
  induction origin with
  | head position => rfl
  | tail origin induction =>
      simp only [ConcreteWireQuantifier.constructionWireDescriptor]
      change ConcreteWireQuantifier.ConstructionWireOrigin.tail
          (constructionWireOriginAt _
            (ConcreteWireQuantifier.constructionWireDescriptor origin).occurrence
            (ConcreteWireQuantifier.constructionWireDescriptor origin).position) =
        ConcreteWireQuantifier.ConstructionWireOrigin.tail origin
      rw [induction]

private theorem rawSourceSites_exists
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (result : ConcreteWireQuantifier.RelationJoinResult source input.wire
      input.content input.parameters) :
    ∃ all,
      checkAllAppliedSites source input.wire = some all := by
  apply checkAllAppliedSites_complete
  intro endpoint member
  obtain ⟨head, region, nodeData⟩ :=
    result.endpoint_applied endpoint member
  exact ⟨head, region, result.args, nodeData⟩

private def rawSourceSites
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (result : ConcreteWireQuantifier.RelationJoinResult source input.wire
      input.content input.parameters) :
    AllAppliedSites source input.wire :=
  match accepted : checkAllAppliedSites source input.wire with
  | some sites => sites
  | none => by
      exfalso
      obtain ⟨sites, complete⟩ := rawSourceSites_exists result
      rw [accepted] at complete
      contradiction

/-- The initial compiler obligation derived solely from checked join evidence
and the raw concrete construction. -/
private def initialRawIntrinsicResidual
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (checked : MonolithicWireQuantifier.Internal.CheckedRelationJoin source
      input.orientation input.wire
      input.content input.parameters)
    (result : ConcreteWireQuantifier.RelationJoinResult source input.wire
      input.content input.parameters) :
    IntrinsicCompilerResidual source
      (ConcreteElaboration.openBoundaryClassSigs input.content.val) :=
  IntrinsicCompilerResidual.initial checked.contentCompilation.compilation
    input.wire checked.arguments checked.sourceSignature
    (rawSourceSites result) input.parameters
    (by simpa [checkedBoundarySigs] using checked.formalSignatures)
    (by simpa [checkedBoundarySigs] using checked.parameterSignatures)
    checked.liveNotParameter

private def retainedAfterErasing
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId) :
    List source.val.WireId :=
  source.val.wiresList.filter fun wire => decide (wire ≠ removed)

/--
Transport an ordered tracked-wire tuple through a replacement that deletes
`removed`, retains all other source wires in order, then appends `freshCount`
wires.  This is the dense-Fin counterpart of the TypeScript allocation map.
-/
private def transportTrackedAfterErase
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (target : CheckedDiagram definitions)
    (freshCount : Nat)
    (tracked : List source.val.WireId) :
    Option { mapped : List target.val.WireId //
      mapped.length = tracked.length } := by
  let retained := retainedAfterErasing source removed
  if countExact :
      target.val.wireCount = retained.length + freshCount then
    let rec go :
        (remaining : List source.val.WireId) →
          Option { mapped : List target.val.WireId //
            mapped.length = remaining.length }
      | [] => some ⟨[], rfl⟩
      | wire :: rest =>
          match Data.Finite.indexOf? retained wire, go rest with
          | some position, some tail =>
              some
                ⟨
                  ⟨position.val, by
                    have positionBound := position.isLt
                    omega⟩ :: tail.val,
                  by simp [tail.property]⟩
          | _, _ => none
    exact go tracked
  else exact none

/-- The `offset`th freshly appended wire after deleting `removed`. -/
private def freshWireAfterErase?
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (target : CheckedDiagram definitions)
    (freshCount offset : Nat) :
    Option target.val.WireId := by
  let retained := retainedAfterErasing source removed
  if offsetBound : offset < freshCount then
    if countExact :
        target.val.wireCount = retained.length + freshCount then
      exact some
        ⟨retained.length + offset, by omega⟩
    else exact none
  else exact none

/-- Transport wire ids through a node/region-only rewrite. -/
private def transportTrackedUnchanged
    (source target : CheckedDiagram definitions)
    (tracked : List source.val.WireId) :
    Option { mapped : List target.val.WireId //
      mapped.length = tracked.length } := by
  if countExact : source.val.wireCount = target.val.wireCount then
    exact some
      ⟨tracked.map fun wire => ⟨wire.val, by omega⟩, by simp⟩
  else exact none

/-- One dependently checked execution together with exact tracked-wire images. -/
structure PrimitiveRun
    (orientation : Orientation)
    (source : CheckedDiagram definitions)
    (trackedCount : Nat) where
  program : PrimitiveProgram orientation source
  tracked : List program.target.val.WireId
  trackedLength : tracked.length = trackedCount

namespace PrimitiveRun

/-- Prefix one checked step to an already compiled continuation. -/
def prepend
    {source : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep orientation source)
    (tail : PrimitiveRun orientation step.target trackedCount) :
    PrimitiveRun orientation source trackedCount where
  program := .cons step tail.program
  tracked := tail.tracked
  trackedLength := tail.trackedLength

/-- Empty execution preserving the caller's ordered tracked tuple. -/
def nil
    (source : CheckedDiagram definitions)
    (tracked : List source.val.WireId) :
    PrimitiveRun orientation source tracked.length where
  program := .nil source
  tracked := tracked
  trackedLength := rfl

end PrimitiveRun

/--
One nonterminal primitive transition: a replacement live wire plus exact
images of the ordered tracked tuple.
-/
private structure LiveStepRun
    (orientation : Orientation)
    (source : CheckedDiagram definitions)
    (trackedCount : Nat) where
  step : CompiledPrimitiveStep orientation source
  live : step.target.val.WireId
  tracked : List step.target.val.WireId
  trackedLength : tracked.length = trackedCount

/-- One terminal primitive transition with exact tracked-wire images. -/
private structure TerminalStepRun
    (orientation : Orientation)
    (source : CheckedDiagram definitions)
    (trackedCount : Nat) where
  step : CompiledPrimitiveStep orientation source
  tracked : List step.target.val.WireId
  trackedLength : tracked.length = trackedCount

private def finishLiveStep
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (step : CompiledPrimitiveStep orientation source)
    (freshCount offset : Nat)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (LiveStepRun orientation source tracked.length) := do
  let live ←
    requireOption .allocationMismatch <|
      freshWireAfterErase? source removed step.target freshCount offset
  let tracked' ←
    requireOption .trackedWireConsumed <|
      transportTrackedAfterErase source removed step.target freshCount tracked
  pure
    { step := step
      live := live
      tracked := tracked'.val
      trackedLength := tracked'.property }

private def finishTerminalStep
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (step : CompiledPrimitiveStep orientation source)
    (freshCount : Nat)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (TerminalStepRun orientation source tracked.length) := do
  let tracked' ←
    requireOption .trackedWireConsumed <|
      transportTrackedAfterErase source removed step.target freshCount tracked
  pure
    { step := step
      tracked := tracked'.val
      trackedLength := tracked'.property }

private def runArityShift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (LiveStepRun orientation source tracked.length) := do
  let applied ←
    (applyArityShift source wire newArgument).mapError
      .argumentRejected
  let step : CompiledPrimitiveStep orientation source :=
    .arityShift wire newArgument applied
  let freshCount := 1 + (source.val.wires wire).endpoints.length
  finishLiveStep source wire step freshCount 0 tracked

private def runCutWrap
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (LiveStepRun orientation source tracked.length) := do
  let applied ←
    (applyCutWrap source wire).mapError .contentRejected
  finishLiveStep source wire
    (.cutWrap wire applied) 1 0 tracked

private structure SplitStepRun
    (orientation : Orientation)
    (source : CheckedDiagram definitions)
    (trackedCount : Nat) where
  step : CompiledPrimitiveStep orientation source
  left : step.target.val.WireId
  right : step.target.val.WireId
  tracked : List step.target.val.WireId
  trackedLength : tracked.length = trackedCount

private def runParallelSplit
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (SplitStepRun orientation source tracked.length) := do
  let applied ←
    (applyParallelSplit source wire).mapError .contentRejected
  let step : CompiledPrimitiveStep orientation source :=
    .parallelSplit wire applied
  let left ←
    requireOption .allocationMismatch <|
      freshWireAfterErase? source wire step.target 2 0
  let right ←
    requireOption .allocationMismatch <|
      freshWireAfterErase? source wire step.target 2 1
  let tracked' ←
    requireOption .trackedWireConsumed <|
      transportTrackedAfterErase source wire step.target 2 tracked
  pure
    { step := step
      left := left
      right := right
      tracked := tracked'.val
      trackedLength := tracked'.property }

private def runArgPermute
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (permutation : List Nat)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (LiveStepRun orientation source tracked.length) := do
  let applied ←
    (applyArgPermute source wire permutation).mapError .argumentRejected
  finishLiveStep source wire
    (.argPermute wire permutation applied) 1 0 tracked

private def runArgDuplicate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (LiveStepRun orientation source tracked.length) := do
  let applied ←
    (applyArgDuplicate source wire position).mapError .argumentRejected
  finishLiveStep source wire
    (.argDuplicate wire position applied) 1 0 tracked

private def runArgDrop
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (LiveStepRun orientation source tracked.length) := do
  let applied ←
    (applyArgDrop source wire position orientation).mapError
      .argumentRejected
  finishLiveStep source wire
    (.argDrop wire position applied) 1 0 tracked

private def runArgExtend
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachment : source.val.WireId)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (LiveStepRun orientation source tracked.length) := do
  let attachments :=
    List.replicate (source.val.wires wire).endpoints.length attachment
  let applied ←
    (applyArgExtend source wire position newArgument attachments orientation)
      |>.mapError .argumentRejected
  finishLiveStep source wire
    (.argExtend wire position newArgument attachments applied) 1 0 tracked

private def runApplyFormal
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (TerminalStepRun orientation source tracked.length) := do
  let applied ←
    (Leaves.applyApplyFormal source wire position orientation).mapError
      .leafRejected
  finishTerminalStep source wire
    (.applyFormal wire position applied) 0 tracked

private def runIdentityLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (TerminalStepRun orientation source tracked.length) := do
  let applied ←
    (Leaves.applyIdentityLeaf source wire orientation).mapError .leafRejected
  finishTerminalStep source wire
    (.identityLeaf wire applied) 0 tracked

private def runRefLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (definition : Fin definitions.length)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (TerminalStepRun orientation source tracked.length) := do
  let applied ←
    (Leaves.applyRefLeaf source wire definition orientation).mapError
      .leafRejected
  finishTerminalStep source wire
    (.refLeaf wire definition applied) 0 tracked

private def runWireJoin
    (source : CheckedDiagram definitions)
    (outer live : source.val.WireId)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (TerminalStepRun orientation source tracked.length) := do
  let input : WireJoinInput source :=
    { orientation := orientation, left := outer, right := live }
  let applied ←
    (applyWireJoin source input).mapError .partitionRejected
  finishTerminalStep source live
    (.wireJoin input rfl applied) 0 tracked

private def runEmptyResidual
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (orientation : Orientation)
    (tracked : List source.val.WireId) :
    Except CompilerError
      (PrimitiveRun orientation source tracked.length) := do
  let deleted ←
    (applyEndsDelete source wire orientation).mapError .contentRejected
  let deleteStep : CompiledPrimitiveStep orientation source :=
    .endsDelete wire deleted
  let carried ←
    requireOption .allocationMismatch <|
      transportTrackedUnchanged source deleteStep.target (wire :: tracked)
  let liveAndTracked := carried.val
  match split : liveAndTracked with
  | [] => throw .allocationMismatch
  | live :: tracked' =>
      let candidate :=
        ConcreteDiagram.DenseErasure.eraseWireCandidate
          deleteStep.target live
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error _ => throw .allocationMismatch
      | .ok plain =>
          have generated : plain.val = candidate :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          have regionCountExact :
              plain.val.regionCount =
                deleteStep.target.val.regionCount := by
            rw [generated]
            simp [candidate,
              ConcreteDiagram.DenseErasure.eraseWireCandidate,
              ConcreteDiagram.regionsList, length_filter_true,
              Data.Finite.allFin_eq_finRange]
          let scope : plain.val.RegionId :=
            ⟨(deleteStep.target.val.wires live).scope.val, by
              rw [regionCountExact]
              exact (deleteStep.target.val.wires live).scope.isLt⟩
          let vacuousInput :
              StructuralCore.VacuousInput plain deleteStep.target :=
            { site := scope
              sig := (deleteStep.target.val.wires live).sig }
          let vacuous ←
            (StructuralCore.checkVacuous vacuousInput).mapError
              .vacuousRejected
          let deletion :
              Vacuity.EliminationReceipt vacuousInput vacuous :=
            Vacuity.recordElimination vacuous live
              (Vacuity.isoOfEq plain.property generated) (by
                apply Fin.ext
                rw [Vacuity.isoOfEq_region_val,
                  ConcreteWireQuantifier.ExhaustedWireRemovalSemantics.targetRegion_val])
              (by rfl) (by
                apply ConcreteWireQuantifier.eraseWireCandidate_wellFormed_implies_endpoints_empty
                change candidate.WellFormed definitions
                rw [← generated]
                exact plain.property)
          let vacuousStep :
              CompiledPrimitiveStep orientation deleteStep.target :=
            .vacuousElim vacuousInput vacuous deletion
          let finalTracked ←
            requireOption .trackedWireConsumed <|
              transportTrackedAfterErase deleteStep.target live
                vacuousStep.target 0 tracked'
          pure
            { program :=
                .cons deleteStep
                  (.cons vacuousStep (.nil vacuousStep.target))
              tracked := finalTracked.val
              trackedLength := by
                have trackedLength : tracked'.length = tracked.length := by
                  have carriedLength :
                      (live :: tracked').length =
                        (wire :: tracked).length := by
                    calc
                      (live :: tracked').length =
                          liveAndTracked.length :=
                        congrArg List.length split.symm
                      _ = carried.val.length := rfl
                      _ = (wire :: tracked).length := carried.property
                  simpa using carriedLength
                exact finalTracked.property.trans trackedLength }

private structure TransportState
    (context : List Sig)
    (target : CheckedDiagram definitions)
    (trackedCount : Nat) where
  tracked : List target.val.WireId
  trackedLength : tracked.length = trackedCount
  ambients :
    List (PackedVar context × target.val.WireId)

private def ambientLookup?
    {source : CheckedDiagram definitions}
    (ambients : List (PackedVar context × source.val.WireId))
    (value : PackedVar context) : Option source.val.WireId :=
  (ambients.find? fun pair => decide (pair.1 = value)).map Prod.snd

private def unpackTransport?
    {context : List Sig}
    {target : CheckedDiagram definitions}
    (ambientStubs : List (PackedVar context))
    (trackedCount : Nat)
    (mapped : List target.val.WireId) :
    Option (TransportState context target trackedCount) := by
  if exact :
      mapped.length = trackedCount + ambientStubs.length then
    exact some
      { tracked := mapped.take trackedCount
        trackedLength := by
          have bound : trackedCount ≤ mapped.length := by omega
          simp [List.length_take, Nat.min_eq_left bound]
        ambients := ambientStubs.zip (mapped.drop trackedCount) }
  else exact none

private def packedTracked
    {context : List Sig}
    {source : CheckedDiagram definitions}
    (tracked : List source.val.WireId)
    (ambients :
      List (PackedVar context × source.val.WireId)) :
    List source.val.WireId :=
  tracked ++ ambients.map Prod.snd

private structure ResidualCompilation
    (orientation : Orientation)
    (source : CheckedDiagram definitions)
    (context : List Sig)
    (trackedCount : Nat) where
  program : PrimitiveProgram orientation source
  tracked : List program.target.val.WireId
  trackedLength : tracked.length = trackedCount
  ambients :
    List (PackedVar context × program.target.val.WireId)
  construction :
    Σ planned : CheckedDiagram definitions,
      ConcreteIso program.target.val planned.val :=
    ⟨program.target,
      Vacuity.identityIso program.target.val program.target.property⟩

namespace ResidualCompilation

/-- Replace the provisional landing by a construction-owned correspondence. -/
private def retarget
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (compiled : ResidualCompilation orientation source context trackedCount)
    (planned : CheckedDiagram definitions)
    (landing : ConcreteIso (definitions := definitions)
      (show CheckedDiagram definitions from compiled.construction.1).val
      planned.val) :
    ResidualCompilation orientation source context trackedCount where
  program := compiled.program
  tracked := compiled.tracked
  trackedLength := compiled.trackedLength
  ambients := compiled.ambients
  construction :=
    ⟨planned, compiled.construction.2.trans landing⟩

private def castTracked
    (compiled :
      ResidualCompilation orientation source context currentCount)
    (exact : currentCount = targetCount) :
    ResidualCompilation orientation source context targetCount where
  program := compiled.program
  tracked := compiled.tracked
  trackedLength := compiled.trackedLength.trans exact
  ambients := compiled.ambients
  construction := compiled.construction

private def prepend
    {source : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep orientation source)
    (tail :
      ResidualCompilation orientation step.target context trackedCount) :
    ResidualCompilation orientation source context trackedCount where
  program := .cons step tail.program
  tracked := tail.tracked
  trackedLength := tail.trackedLength
  ambients := tail.ambients
  construction := tail.construction

end ResidualCompilation

private def combineParallel
    {source : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep orientation source)
    (leftProgram : PrimitiveProgram orientation step.target)
    (right :
      ResidualCompilation orientation leftProgram.target context currentCount)
    (countExact : currentCount = targetCount) :
    ResidualCompilation orientation source context targetCount := by
  let right' := right.castTracked countExact
  let tailProgram := leftProgram.append right'.program
  let finalProgram := PrimitiveProgram.cons step tailProgram
  have finalTarget : finalProgram.target = right'.program.target := by
    simp only [finalProgram, PrimitiveProgram.target, tailProgram,
      PrimitiveProgram.target_append]
  exact
    { program := finalProgram
      tracked := castWireList finalTarget.symm right'.tracked
      trackedLength := by
        rw [castWireList_length]
        exact right'.trackedLength
      ambients := by
        rw [finalTarget]
        exact right'.ambients
      construction := by
        rw [finalTarget]
        exact right'.construction }

private def terminalCompilation
    (context : List Sig)
    (trackedCount : Nat)
    (ambientStubs : List (PackedVar context))
    (terminal : TerminalStepRun orientation source
      (trackedCount + ambientStubs.length)) :
    Except CompilerError
      (ResidualCompilation orientation source context trackedCount) := do
  let transported ←
    requireOption .allocationMismatch <|
      unpackTransport? ambientStubs trackedCount terminal.tracked
  pure
    { program := .cons terminal.step (.nil terminal.step.target)
      tracked := transported.tracked
      trackedLength := transported.trackedLength
      ambients := transported.ambients }

private def primitiveCompilation
    (context : List Sig)
    (trackedCount : Nat)
    (ambientStubs : List (PackedVar context))
    (run : PrimitiveRun orientation source
      (trackedCount + ambientStubs.length)) :
    Except CompilerError
      (ResidualCompilation orientation source context trackedCount) := do
  let transported ←
    requireOption .allocationMismatch <|
      unpackTransport? ambientStubs trackedCount run.tracked
  pure
    { program := run.program
      tracked := transported.tracked
      trackedLength := transported.trackedLength
      ambients := transported.ambients }

/-- One content-side argument-normalization instruction. -/
private inductive PlumbingOp
    (context : List Sig)
  | extend (stub : PackedVar context) (position : Nat)
  | drop (position : Nat)
  | permute (permutation : List Nat)
  | duplicate (position : Nat)

private def eraseAt : Nat → List α → List α
  | _, [] => []
  | 0, _ :: tail => tail
  | position + 1, head :: tail => head :: eraseAt position tail

private def insertAt : Nat → α → List α → List α
  | 0, value, values => value :: values
  | _ + 1, value, [] => [value]
  | position + 1, value, head :: tail =>
      head :: insertAt position value tail

private def moveAt?
    (values : List α) (source target : Nat) : Option (List α) := do
  let value ← values[source]?
  pure (insertAt target value (eraseAt source values))

private structure PlumbingPlan
    (context : List Sig) where
  positions : List (PackedVar context)
  operations : List (PlumbingOp context)

private def materializePlan
    (context : List Sig)
    (initial target : List (PackedVar context)) :
    PlumbingPlan context :=
  target.foldl
    (fun plan stub =>
      if stub ∈ plan.positions then
        plan
      else
        { positions := plan.positions ++ [stub]
          operations :=
            plan.operations ++ [.extend stub plan.positions.length] })
    { positions := initial, operations := [] }

private def dropUnusedPlan
    (target : List (PackedVar context))
    (initial : PlumbingPlan context) :
    PlumbingPlan context :=
  (List.range initial.positions.length).reverse.foldl
    (fun plan position =>
      match plan.positions[position]? with
      | none => plan
      | some stub =>
          if stub ∈ target then
            plan
          else
            { positions := eraseAt position plan.positions
              operations := plan.operations ++ [.drop position] })
    initial

private def arrangeOne
    (target : List (PackedVar context))
    (plan : PlumbingPlan context)
    (position : Nat) :
    Option (PlumbingPlan context) := do
  let wanted ← target[position]?
  match plan.positions[position]? with
  | some current =>
      if current = wanted then
        pure plan
      else
        let found ← Data.Finite.indexOf? plan.positions wanted
        if found.val < position then
          let duplicated :=
            insertAt (found.val + 1) wanted plan.positions
          let afterDuplicate : PlumbingPlan context :=
            { positions := duplicated
              operations :=
                plan.operations ++ [.duplicate found.val] }
          if found.val + 1 = position then
            pure afterDuplicate
          else
            let positions ←
              moveAt? afterDuplicate.positions (found.val + 1) position
            let permutation ←
              moveAt? (List.range afterDuplicate.positions.length)
                (found.val + 1) position
            pure
              { positions := positions
                operations :=
                  afterDuplicate.operations ++ [.permute permutation] }
        else
          let positions ← moveAt? plan.positions found.val position
          let permutation ←
            moveAt? (List.range plan.positions.length) found.val position
          pure
            { positions := positions
              operations := plan.operations ++ [.permute permutation] }
  | none =>
      let found ← Data.Finite.indexOf? plan.positions wanted
      if found.val < position then
        let duplicated :=
          insertAt (found.val + 1) wanted plan.positions
        let afterDuplicate : PlumbingPlan context :=
          { positions := duplicated
            operations :=
              plan.operations ++ [.duplicate found.val] }
        if found.val + 1 = position then
          pure afterDuplicate
        else
          let positions ←
            moveAt? afterDuplicate.positions (found.val + 1) position
          let permutation ←
            moveAt? (List.range afterDuplicate.positions.length)
              (found.val + 1) position
          pure
            { positions := positions
              operations :=
                afterDuplicate.operations ++ [.permute permutation] }
      else
        none

private def arrangePlan
    (target : List (PackedVar context))
    (initial : PlumbingPlan context) :
    Option (PlumbingPlan context) :=
  (List.range target.length).foldlM (arrangeOne target) initial

/--
Plan exact tuple normalization solely from content identifiers.  The
primitive checkers subsequently validate every emitted operation against the
live host diagram.
-/
private def planPlumbing
    (context : List Sig)
    (initial target : List (PackedVar context)) :
    Option (List (PlumbingOp context)) := do
  let materialized := materializePlan context initial target
  let dropped := dropUnusedPlan target materialized
  let arranged ← arrangePlan target dropped
  if arranged.positions = target then
    pure arranged.operations
  else
    none

private structure LiveResidualCompilation
    (orientation : Orientation)
    (source : CheckedDiagram definitions)
    (context : List Sig)
    (trackedCount : Nat) where
  program : PrimitiveProgram orientation source
  live : program.target.val.WireId
  tracked : List program.target.val.WireId
  trackedLength : tracked.length = trackedCount
  ambients :
    List (PackedVar context × program.target.val.WireId)

namespace LiveResidualCompilation

private def castTracked
    (compiled :
      LiveResidualCompilation orientation source context currentCount)
    (exact : currentCount = targetCount) :
    LiveResidualCompilation orientation source context targetCount where
  program := compiled.program
  live := compiled.live
  tracked := compiled.tracked
  trackedLength := compiled.trackedLength.trans exact
  ambients := compiled.ambients

private def prepend
    {source : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep orientation source)
    (tail :
      LiveResidualCompilation orientation step.target context trackedCount) :
    LiveResidualCompilation orientation source context trackedCount where
  program := .cons step tail.program
  live := tail.live
  tracked := tail.tracked
  trackedLength := tail.trackedLength
  ambients := tail.ambients

end LiveResidualCompilation

private def executePlumbing
    {definitions : List (List Sig)}
    {context : List Sig} :
    (operations : List (PlumbingOp context)) →
    (source : CheckedDiagram definitions) →
    (wire : source.val.WireId) →
    (ambients :
      List (PackedVar context × source.val.WireId)) →
    (tracked : List source.val.WireId) →
    (orientation : Orientation) →
    Except CompilerError
      (LiveResidualCompilation orientation source context tracked.length)
  | [], source, wire, ambients, tracked, _ =>
      .ok
        { program := .nil source
          live := wire
          tracked := tracked
          trackedLength := rfl
          ambients := ambients }
  | operation :: rest, source, wire, ambients, tracked, orientation => do
      let ambientStubs := ambients.map Prod.fst
      let packed := packedTracked tracked ambients
      let stepRun ←
        match operation with
        | .extend stub position =>
            let attachment ←
              requireOption .missingAmbient <|
                ambientLookup? ambients stub
            runArgExtend source wire position
              stub.1 attachment orientation packed
        | .drop position =>
            runArgDrop source wire position orientation packed
        | .permute permutation =>
            runArgPermute source wire permutation orientation packed
        | .duplicate position =>
            runArgDuplicate source wire position orientation packed
      let transported ←
        requireOption .allocationMismatch <|
          unpackTransport? ambientStubs tracked.length stepRun.tracked
      let tail ←
        executePlumbing rest stepRun.step.target stepRun.live
          transported.ambients transported.tracked orientation
      pure
        ((tail.castTracked transported.trackedLength).prepend stepRun.step)

private def finishPlumbed
    (context : List Sig)
    (plumbed :
      LiveResidualCompilation orientation source context trackedCount)
    (terminal :
      TerminalStepRun orientation plumbed.program.target
        (plumbed.tracked.length + plumbed.ambients.length)) :
    Except CompilerError
      (ResidualCompilation orientation source context trackedCount) := do
  let ambientStubs := plumbed.ambients.map Prod.fst
  let transported ←
    requireOption .allocationMismatch <|
      unpackTransport? ambientStubs plumbed.tracked.length terminal.tracked
  let terminalProgram :=
    PrimitiveProgram.cons terminal.step (.nil terminal.step.target)
  let finalProgram := plumbed.program.append terminalProgram
  have finalTarget : finalProgram.target = terminal.step.target :=
    PrimitiveProgram.target_append plumbed.program terminalProgram
  pure
    { program := finalProgram
      tracked := castWireList finalTarget.symm transported.tracked
      trackedLength := by
        rw [castWireList_length]
        exact
          transported.trackedLength.trans plumbed.trackedLength
      ambients := by
        rw [finalTarget]
        exact transported.ambients }

private def defVarIndex :
    {arguments : List Sig} → DefVar definitions arguments →
      Fin definitions.length
  | _, .here => ⟨0, by simp⟩
  | _, .there tail =>
      let index := defVarIndex tail
      ⟨index.val + 1, by simp only [List.length_cons]; omega⟩

/-- The executable part of the proof-carrying intrinsic obligation. -/
private structure IntrinsicExecutionResidual
    (source : CheckedDiagram definitions)
    (context : List Sig) where
  body : Region definitions context
  wire : source.val.WireId
  formals : List (PackedVar context)
  ambients : List (PackedVar context × source.val.WireId)

/-- Executable projection of the plan-mandated structural/plumbing measure. -/
private def IntrinsicExecutionResidual.measure
    (residual : IntrinsicExecutionResidual source context) : Nat × Nat :=
  (intrinsicRegionSize residual.body,
    residual.formals.length + residual.ambients.length)

private def IntrinsicCompilerResidual.execution
    (residual : IntrinsicCompilerResidual source context) :
    IntrinsicExecutionResidual source context where
  body := residual.body
  wire := residual.wire
  formals := residual.formals
  ambients := residual.ambients.map fun binding =>
    (binding.value, binding.wire)

@[simp]
private theorem IntrinsicCompilerResidual.execution_measure
    (residual : IntrinsicCompilerResidual source context) :
    residual.execution.measure = residual.measure := by
  simp [IntrinsicExecutionResidual.measure,
    IntrinsicCompilerResidual.execution, IntrinsicCompilerResidual.measure]

private def lowerPackedVar?
    (value : PackedVar (bound :: context)) : Option (PackedVar context) :=
  match value with
  | ⟨_, .here⟩ => none
  | ⟨signature, .there outer⟩ => some ⟨signature, outer⟩

private def lowerAmbients?
    {source : CheckedDiagram definitions}
    (ambients : List (PackedVar (bound :: context) × source.val.WireId)) :
    Option (List (PackedVar context × source.val.WireId)) :=
  ambients.mapM fun binding => do
    let value ← lowerPackedVar? binding.1
    pure (value, binding.2)

private theorem intrinsicItemSize_positive
    (item : Item definitions context) : 0 < intrinsicItemSize item := by
  cases item <;> simp [intrinsicItemSize] <;> omega

private theorem intrinsicHead_smaller
    (head next : Item definitions context)
    (rest : ItemSeq definitions context) :
    intrinsicItemSize head <
      intrinsicItemSize head +
        (intrinsicItemSize next + intrinsicItemSeqSize rest) := by
  have positive := intrinsicItemSize_positive next
  omega

private theorem intrinsicTail_smaller
    (head next : Item definitions context)
    (rest : ItemSeq definitions context) :
    intrinsicItemSize next + intrinsicItemSeqSize rest <
      intrinsicItemSize head +
        (intrinsicItemSize next + intrinsicItemSeqSize rest) := by
  have positive := intrinsicItemSize_positive head
  omega

private def compileIntrinsicLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (formals : List (PackedVar context))
    (ambients : List (PackedVar context × source.val.WireId))
    (item : Item definitions context)
    (tracked : List source.val.WireId)
    (orientation : Orientation) :
    Except CompilerError
      (ResidualCompilation orientation source context tracked.length) := do
  match item with
  | .atom head arguments =>
      let headValue : PackedVar context := ⟨.rel _, head⟩
      let argumentValues := arguments.entries
      if _formal : headValue ∈ formals then
        let operations ←
          requireOption .malformedResidual <|
            planPlumbing context formals (headValue :: argumentValues)
        let plumbed ←
          executePlumbing operations source wire ambients tracked orientation
        let packed := packedTracked plumbed.tracked plumbed.ambients
        let terminal ←
          runApplyFormal plumbed.program.target plumbed.live 0 orientation
            packed
        finishPlumbed context plumbed
          (by simpa [packed, packedTracked] using terminal)
      else
        let _fixed ←
          requireOption .missingAmbient <|
            ambientLookup? ambients headValue
        let operations ←
          requireOption .malformedResidual <|
            planPlumbing context formals argumentValues
        let plumbed ←
          executePlumbing operations source wire ambients tracked orientation
        let fixed ←
          requireOption .missingAmbient <|
            ambientLookup? plumbed.ambients headValue
        let packed := packedTracked plumbed.tracked plumbed.ambients
        let terminal ←
          runWireJoin plumbed.program.target fixed plumbed.live orientation
            packed
        finishPlumbed context plumbed
          (by simpa [packed, packedTracked] using terminal)
  | .named definition arguments =>
      let operations ←
        requireOption .malformedResidual <|
          planPlumbing context formals arguments.entries
      let plumbed ←
        executePlumbing operations source wire ambients tracked orientation
      let packed := packedTracked plumbed.tracked plumbed.ambients
      let terminal ←
        runRefLeaf plumbed.program.target plumbed.live
          (defVarIndex definition) orientation packed
      finishPlumbed context plumbed
        (by simpa [packed, packedTracked] using terminal)
  | .identity signature ports _ =>
      let portValues : List (PackedVar context) :=
        ports.map fun port => ⟨signature, port⟩
      let operations ←
        requireOption .malformedResidual <|
          planPlumbing context formals portValues
      let plumbed ←
        executePlumbing operations source wire ambients tracked orientation
      let packed := packedTracked plumbed.tracked plumbed.ambients
      let terminal ←
        runIdentityLeaf plumbed.program.target plumbed.live orientation packed
      finishPlumbed context plumbed
        (by simpa [packed, packedTracked] using terminal)
  | .cut _ => throw .malformedResidual
  | .bind _ _ => throw .malformedResidual

private def compileIntrinsicResidual :
    (source : CheckedDiagram definitions) →
    (residual : IntrinsicExecutionResidual source context) →
    (tracked : List source.val.WireId) →
    (orientation : Orientation) →
    Except CompilerError
      (ResidualCompilation orientation source context tracked.length)
  | source, residual, tracked, orientation => do
      let ambientValues := residual.ambients.map Prod.fst
      let packed := packedTracked tracked residual.ambients
      match bodyExact : residual.body with
      | .mk (.cons (.bind signature body) .nil) =>
          let shifted ←
            runArityShift source residual.wire signature orientation packed
          let transported ←
            requireOption .allocationMismatch <|
              unpackTransport? ambientValues tracked.length shifted.tracked
          let nested : IntrinsicExecutionResidual shifted.step.target
              (signature :: context) :=
            { body := body
              wire := shifted.live
              formals :=
                residual.formals.map
                    (liftPackedVar (bound := signature)) ++
                  [⟨signature, .here⟩]
              ambients := transported.ambients.map fun binding =>
                (liftPackedVar (bound := signature) binding.1, binding.2) }
          let tail ←
            compileIntrinsicResidual shifted.step.target nested
              transported.tracked orientation
          let lowered ←
            requireOption .malformedResidual <| lowerAmbients? tail.ambients
          let loweredTail :
              ResidualCompilation orientation shifted.step.target context
                transported.tracked.length :=
            { program := tail.program
              tracked := tail.tracked
              trackedLength := tail.trackedLength
              ambients := lowered
              construction := tail.construction }
          pure
            ((loweredTail.castTracked transported.trackedLength).prepend
              shifted.step)
      | .mk .nil =>
          let emptied ←
            runEmptyResidual source residual.wire orientation packed
          let emptied' : PrimitiveRun orientation source
              (tracked.length + ambientValues.length) :=
            { program := emptied.program
              tracked := emptied.tracked
              trackedLength := by
                simpa [packed, packedTracked, ambientValues] using
                  emptied.trackedLength }
          primitiveCompilation context tracked.length ambientValues
            emptied'
      | .mk (.cons (.cut body) .nil) =>
          let wrapped ←
            runCutWrap source residual.wire orientation packed
          let transported ←
            requireOption .allocationMismatch <|
              unpackTransport? ambientValues tracked.length wrapped.tracked
          let nested : IntrinsicExecutionResidual wrapped.step.target context :=
            { body := body
              wire := wrapped.live
              formals := residual.formals
              ambients := transported.ambients }
          let tail ←
            compileIntrinsicResidual wrapped.step.target nested
              transported.tracked orientation
          pure
            ((tail.castTracked transported.trackedLength).prepend wrapped.step)
      | .mk (.cons item .nil) =>
          compileIntrinsicLeaf source residual.wire residual.formals
            residual.ambients item tracked orientation
      | .mk (.cons head (.cons next rest)) =>
          let split ←
            runParallelSplit source residual.wire orientation packed
          let transported ←
            requireOption .allocationMismatch <|
              unpackTransport? ambientValues tracked.length split.tracked
          let leftResidual :
              IntrinsicExecutionResidual split.step.target context :=
            { body := .mk (.cons head .nil)
              wire := split.left
              formals := residual.formals
              ambients := transported.ambients }
          let left ←
            compileIntrinsicResidual split.step.target leftResidual
              (split.right :: transported.tracked) orientation
          match rightSplit : left.tracked with
          | [] => throw .allocationMismatch
          | right :: remainingTracked =>
              let rightResidual :
                  IntrinsicExecutionResidual left.program.target context :=
                { body := .mk (.cons next rest)
                  wire := right
                  formals := residual.formals
                  ambients := left.ambients }
              let rightCompiled ←
                compileIntrinsicResidual left.program.target rightResidual
                  remainingTracked orientation
              have remainingLength :
                  remainingTracked.length = tracked.length := by
                have leftLength := left.trackedLength
                rw [rightSplit] at leftLength
                have transportedLength := transported.trackedLength
                simp only [List.length_cons] at leftLength
                omega
              pure
                (combineParallel split.step left.program rightCompiled
                  remainingLength)
termination_by source residual tracked orientation =>
  residual.measure
decreasing_by
  all_goals
    try simp_all [IntrinsicExecutionResidual.measure, bodyExact,
      intrinsicRegionSize, intrinsicItemSeqSize, intrinsicItemSize]
  all_goals
    try
      have headPositive := intrinsicItemSize_positive head
      have nextPositive := intrinsicItemSize_positive next
      omega
  all_goals omega

private def compileResidual
    (residual : IntrinsicCompilerResidual source context)
    (tracked : List source.val.WireId)
    (orientation : Orientation) :
    Except CompilerError
      (ResidualCompilation orientation source context tracked.length) :=
  compileIntrinsicResidual source residual.execution tracked orientation

private structure InverseStepRun
    (orientation : Orientation)
    (real planned : CheckedDiagram definitions) where
  step : CompiledPrimitiveStep orientation real
  constructionIso : ConcreteIso step.target.val planned.val

private def invertStep
    {planned : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep joinOrientation planned)
    (real : CheckedDiagram definitions)
    (targetIso : ConcreteIso real.val step.target.val)
    (orientation : Orientation) :
    Except CompilerError (InverseStepRun orientation real planned) :=
  match step with
  | .wireSever input _ applied => do
      let inverse ←
        (Partition.invertWireSeverTransported applied real targetIso
          orientation).mapError .partitionRejected
      pure
        { step := .wireJoin inverse.input inverse.orientationExact
            inverse.applied
          constructionIso := inverse.targetIso }
  | .wireJoin _ _ applied => do
      let inverse ←
        (Partition.invertWireJoinTransported applied real targetIso
          orientation).mapError .partitionRejected
      pure
        { step := .wireSever inverse.input inverse.orientationExact
            inverse.applied
          constructionIso := inverse.targetIso }
  | .arityShift _ _ applied => do
      let inverseWire := targetIso.wires.symm applied.targetWire
      let wireExact := targetIso.wires.right_inv applied.targetWire
      let inversePosition := applied.sourceArgumentList.length
      let inverseApplied ←
        (applyArityUnshift real inverseWire inversePosition).mapError
          .argumentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .arityUnshift inverseWire inversePosition inverseApplied
      let constructionIso := applied.inverseTransportIso inverseApplied
        targetIso wireExact
      pure { step := inverseStep, constructionIso := constructionIso }
  | .argPermute _ _ applied => do
      let inverseWire := targetIso.wires.symm applied.targetWire
      let inverse := applied.inversePermutation
      let inverseApplied ←
        (applyArgPermute real inverseWire inverse).mapError
          .argumentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .argPermute inverseWire inverse inverseApplied
      let constructionIso := applied.inverseTransportIso inverseApplied
        targetIso (targetIso.wires.right_inv applied.targetWire)
      pure { step := inverseStep, constructionIso := constructionIso }
  | .argDrop _ position applied => do
      match argumentExact : applied.sourceArgumentList[position]? with
      | none => throw .malformedResidual
      | some signature =>
          let inverseWire := targetIso.wires.symm applied.targetWire
          let wireExact := targetIso.wires.right_inv applied.targetWire
          let inverseAttachments :=
            applied.inverseAttachments targetIso wireExact
          let inverseApplied ←
            (applyArgExtend real inverseWire position signature
              inverseAttachments orientation).mapError .argumentRejected
          let inverseStep : CompiledPrimitiveStep orientation real :=
            .argExtend inverseWire position signature inverseAttachments
              inverseApplied
          let constructionIso := applied.inverseTransportIso targetIso wireExact
            inverseApplied argumentExact
          pure { step := inverseStep, constructionIso := constructionIso }
  | .argExtend _ position _ _ applied => do
      let inverseWire := targetIso.wires.symm applied.targetWire
      let wireExact := targetIso.wires.right_inv applied.targetWire
      let inverseApplied ←
        (applyArgDrop real inverseWire position orientation).mapError
          .argumentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .argDrop inverseWire position inverseApplied
      let constructionIso := applied.inverseTransportIso inverseApplied targetIso
        wireExact
      pure { step := inverseStep, constructionIso := constructionIso }
  | .applyFormal _ _ applied => do
      let inverseNodes :=
        applied.inverseNodes.map targetIso.nodes.symm
      let inverseScope := targetIso.regions.symm applied.inverseScope
      let inverseApplied ←
        (Leaves.applyAbstractFormal real inverseNodes inverseScope orientation)
          |>.mapError .leafRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .abstractFormal inverseNodes inverseScope inverseApplied
      let landing ←
        (applied.inverseTransport inverseApplied targetIso).mapError
          .leafRejected
      let constructionIso := landing.iso
      pure { step := inverseStep, constructionIso := constructionIso }
  | .identityLeaf _ applied => do
      let inverseNodes :=
        applied.inverseNodes.map targetIso.nodes.symm
      let inverseScope := targetIso.regions.symm applied.inverseScope
      let inverseApplied ←
        (Leaves.applyIdentityAbstract real inverseNodes inverseScope
          orientation).mapError .leafRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .identityAbstract inverseNodes inverseScope inverseApplied
      let landing ←
        (applied.inverseTransport inverseApplied targetIso).mapError
          .leafRejected
      let constructionIso := landing.iso
      pure { step := inverseStep, constructionIso := constructionIso }
  | .refLeaf _ _ applied => do
      let inverseNodes :=
        applied.inverseNodes.map targetIso.nodes.symm
      let inverseScope := targetIso.regions.symm applied.inverseScope
      let inverseApplied ←
        (Leaves.applyRefAbstract real inverseNodes inverseScope orientation)
          |>.mapError .leafRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .refAbstract inverseNodes inverseScope inverseApplied
      let landing ←
        (applied.inverseTransport inverseApplied targetIso).mapError
          .leafRejected
      let constructionIso := landing.iso
      pure { step := inverseStep, constructionIso := constructionIso }
  | .endsDelete _ applied => do
      let inverseWire := applied.transportedInverseWire targetIso
      let inverseSites := applied.transportedInverseSites targetIso
      let inverseApplied ←
        (applyEndsSpawn real inverseWire inverseSites orientation).mapError
          .contentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .endsSpawn inverseWire inverseSites inverseApplied
      let landing ←
        (applied.inverseTransport targetIso inverseApplied).mapError
          .contentRejected
      let constructionIso := landing.iso
      pure { step := inverseStep, constructionIso := constructionIso }
  | .cutWrap _ applied => do
      let inverseWire := applied.transportedInverseWire targetIso
      let inverseApplied ←
        (applyCutAbsorb real inverseWire).mapError .contentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .cutAbsorb inverseWire inverseApplied
      let landing ←
        (applied.inverseTransport targetIso inverseApplied).mapError
          .contentRejected
      let constructionIso := landing.iso
      pure { step := inverseStep, constructionIso := constructionIso }
  | .parallelSplit _ applied => do
      let inverseLeft := applied.transportedInverseLeft targetIso
      let inverseRight := applied.transportedInverseRight targetIso
      let inverseApplied ←
        (applyParallelFuse real inverseLeft inverseRight).mapError
          .contentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .parallelFuse inverseLeft inverseRight inverseApplied
      let landing ←
        (applied.inverseTransport targetIso inverseApplied).mapError
          .contentRejected
      let constructionIso := landing.iso
      pure { step := inverseStep, constructionIso := constructionIso }
  | .argDuplicate _ position applied => do
      let inverseWire := targetIso.wires.symm applied.targetWire
      let wireExact := targetIso.wires.right_inv applied.targetWire
      let inverseApplied ←
        (applyArgContract real inverseWire position).mapError
          .argumentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .argContract inverseWire position inverseApplied
      let constructionIso := applied.inverseTransportIso inverseApplied targetIso
        wireExact
      pure { step := inverseStep, constructionIso := constructionIso }
  | .vacuousElim input _ deletion => do
      let inverseSite := targetIso.regions.symm input.site
      let inverseInput : StructuralCore.VacuousInput real planned :=
        { site := inverseSite, sig := input.sig }
      let inverseChecked ←
        (StructuralCore.checkVacuous inverseInput).mapError
          .vacuousRejected
      let inverseDeletion :
          Vacuity.EliminationReceipt inverseInput inverseChecked :=
        Vacuity.transportElimination deletion real targetIso inverseInput
          inverseChecked rfl rfl
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .vacuousIntro inverseInput inverseChecked inverseDeletion
      let constructionIso := Vacuity.identityIso planned.val planned.property
      pure { step := inverseStep, constructionIso := constructionIso }
  | _ => throw .malformedResidual

private def reversePrimitiveProgram :
    {planned : CheckedDiagram definitions} →
    (program : PrimitiveProgram joinOrientation planned) →
    (real : CheckedDiagram definitions) →
    ConcreteIso program.target.val real.val →
    (orientation : Orientation) →
    Except CompilerError
      (PrimitiveProgram.ConstructionLanding orientation real planned)
  | planned, .nil _, real, finalIso, _ =>
      .ok
        { program := .nil real
          constructionIso := finalIso.symm }
  | planned, .cons head tail, real, finalIso, orientation => do
      let reversedTail ←
        reversePrimitiveProgram tail real finalIso orientation
      let inverse ←
        invertStep head reversedTail.program.target
          reversedTail.constructionIso orientation
      pure
        { program :=
            reversedTail.program.append
              (.cons inverse.step (.nil inverse.step.target))
          constructionIso := by
            simpa only [PrimitiveProgram.target_append] using
              inverse.constructionIso }

/-- Read a compiled region through a proposed raw terminal-origin carrier. -/
private def compiledRegionData
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (compiled : CheckedDiagram definitions)
    {result : ConcreteWireQuantifier.RelationJoinResult source dying content
      parameters}
    (regions : Data.Finite.FiniteEquiv compiled.val.RegionId
      (ConcreteWireQuantifier.RelationJoinResult.FinalRegionOrigin result))
    (region : compiled.val.RegionId) :
    ConcreteWireQuantifier.AtlasRegionData
      (ConcreteWireQuantifier.RelationJoinResult.FinalRegionOrigin result) :=
  match compiled.val.regions region with
  | .sheet => .sheet
  | .cut parent => .cut (regions parent)

/-- Read a compiled node through proposed raw terminal-origin carriers. -/
private def compiledNodeData
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (compiled : CheckedDiagram definitions)
    {result : ConcreteWireQuantifier.RelationJoinResult source dying content
      parameters}
    (regions : Data.Finite.FiniteEquiv compiled.val.RegionId
      (ConcreteWireQuantifier.RelationJoinResult.FinalRegionOrigin result))
    (node : compiled.val.NodeId) :
    ConcreteWireQuantifier.AtlasNodeData
      (ConcreteWireQuantifier.RelationJoinResult.FinalRegionOrigin result)
        definitions.length :=
  match compiled.val.nodes node with
  | .atom region args => .atom (regions region) args
  | .ref region definition args => .ref (regions region) definition args
  | .identity region signature arity =>
      .identity (regions region) signature arity

/-- Classify one compiled endpoint by its proposed raw terminal node origin. -/
private def compiledEndpointOrigin
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (compiled : CheckedDiagram definitions)
    {result : ConcreteWireQuantifier.RelationJoinResult source dying content
      parameters}
    (nodes : Data.Finite.FiniteEquiv compiled.val.NodeId
      (ConcreteWireQuantifier.RelationJoinResult.FinalNodeOrigin result))
    (endpoint : CEndpoint compiled.val.nodeCount) :
    ConcreteWireQuantifier.RawEndpoint
      (ConcreteWireQuantifier.RelationJoinResult.FinalNodeOrigin result) :=
  { node := nodes endpoint.node, port := endpoint.port }

/-- The minimum terminal facts from the primitive construction needed by
`ConcreteIso.ofEquivs`.  Every field is consumed by `constructionIso` below;
the receipt introduces no second graph representation or search procedure. -/
private structure RawJoinConstructionConformance
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (compiled : CheckedDiagram definitions)
    (result : ConcreteWireQuantifier.RelationJoinResult source dying content
      parameters) where
  regions : Data.Finite.FiniteEquiv compiled.val.RegionId
    (ConcreteWireQuantifier.RelationJoinResult.FinalRegionOrigin result)
  nodes : Data.Finite.FiniteEquiv compiled.val.NodeId
    (ConcreteWireQuantifier.RelationJoinResult.FinalNodeOrigin result)
  wires : Data.Finite.FiniteEquiv compiled.val.WireId
    (ConcreteWireQuantifier.FinalWireOrigin result)
  root : regions compiled.val.root =
    result.finalRegionOriginEquiv result.plainFinal.val.root
  regionData : ∀ region,
    compiledRegionData compiled regions region =
      ConcreteWireQuantifier.expectedRegionData result.steps (regions region)
  nodeData : ∀ node,
    compiledNodeData compiled regions node =
      ConcreteWireQuantifier.expectedNodeData (definitions := definitions)
        (source := source) (dying := dying) (content := content)
        result.steps (nodes node).1
  wireSignature : ∀ wire,
    (compiled.val.wires wire).sig =
      ConcreteWireQuantifier.expectedFinalWireSignature result (wires wire)
  wireScope : ∀ wire,
    regions (compiled.val.wires wire).scope =
      ConcreteWireQuantifier.expectedFinalWireScope result (wires wire)
  wireEndpoints : ∀ wire,
    (compiled.val.wires wire).endpoints.map
        (compiledEndpointOrigin compiled nodes) =
      ConcreteWireQuantifier.expectedFinalWireEndpoints result (wires wire)

namespace RawJoinConstructionConformance

private def regionEquiv
    (conformance : RawJoinConstructionConformance compiled result) :
    Data.Finite.FiniteEquiv compiled.val.RegionId
      result.plainFinal.val.RegionId :=
  conformance.regions.trans result.finalRegionOriginEquiv.symm

private def nodeEquiv
    (conformance : RawJoinConstructionConformance compiled result) :
    Data.Finite.FiniteEquiv compiled.val.NodeId
      result.plainFinal.val.NodeId :=
  conformance.nodes.trans result.finalNodeOriginEquiv.symm

private def wireEquiv
    (conformance : RawJoinConstructionConformance compiled result) :
    Data.Finite.FiniteEquiv compiled.val.WireId
      result.plainFinal.val.WireId :=
  conformance.wires.trans
    (ConcreteWireQuantifier.finalWireOriginEquiv result).symm

private theorem root_exact
    (conformance : RawJoinConstructionConformance compiled result) :
    conformance.regionEquiv compiled.val.root =
      result.plainFinal.val.root := by
  change result.finalRegionOriginEquiv.symm
      (conformance.regions compiled.val.root) =
    result.plainFinal.val.root
  apply result.finalRegionOriginEquiv.injective
  rw [result.finalRegionOriginEquiv.apply_symm_apply]
  exact conformance.root

private theorem region_eq_regionEquiv_iff
    (conformance : RawJoinConstructionConformance compiled result)
    (rawRegion : result.plainFinal.val.RegionId)
    (compiledRegion : compiled.val.RegionId) :
    rawRegion = conformance.regionEquiv compiledRegion ↔
      result.finalRegionOriginEquiv rawRegion =
        conformance.regions compiledRegion := by
  constructor
  · intro exact
    rw [exact]
    exact result.finalRegionOriginEquiv.apply_symm_apply _
  · intro exact
    apply result.finalRegionOriginEquiv.injective
    change result.finalRegionOriginEquiv rawRegion =
      result.finalRegionOriginEquiv
        (result.finalRegionOriginEquiv.symm
          (conformance.regions compiledRegion))
    rw [result.finalRegionOriginEquiv.apply_symm_apply]
    exact exact

private theorem region_eq_originInverse_iff
    (conformance : RawJoinConstructionConformance compiled result)
    (rawRegion : result.plainFinal.val.RegionId)
    (compiledRegion : compiled.val.RegionId) :
    rawRegion = result.finalRegionOriginEquiv.symm
        (conformance.regions compiledRegion) ↔
      result.finalRegionOriginEquiv rawRegion =
        conformance.regions compiledRegion := by
  simpa [regionEquiv] using
    conformance.region_eq_regionEquiv_iff rawRegion compiledRegion

private theorem region_table
    (conformance : RawJoinConstructionConformance compiled result)
    (region : compiled.val.RegionId) :
    result.plainFinal.val.regions (conformance.regionEquiv region) =
      (compiled.val.regions region).rename conformance.regionEquiv := by
  have rawExact :=
    result.plainRegionData_exact (conformance.regionEquiv region)
  have compiledExact := conformance.regionData region
  have originExact :
      result.finalRegionOriginEquiv (conformance.regionEquiv region) =
        conformance.regions region := by
    exact result.finalRegionOriginEquiv.apply_symm_apply _
  rw [originExact] at rawExact
  have same := rawExact.trans compiledExact.symm
  cases compiledData : compiled.val.regions region with
  | sheet =>
      cases rawData : result.plainFinal.val.regions
          (conformance.regionEquiv region) with
      | sheet => rfl
      | cut parent =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainRegionData,
            compiledRegionData, compiledData, rawData] at same
  | cut compiledParent =>
      cases rawData : result.plainFinal.val.regions
          (conformance.regionEquiv region) with
      | sheet =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainRegionData,
            compiledRegionData, compiledData, rawData] at same
      | cut rawParent =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainRegionData,
            compiledRegionData, compiledData, rawData] at same
          simp [compiledData, CRegion.rename]
          exact (conformance.region_eq_regionEquiv_iff
            rawParent compiledParent).mpr same

private theorem node_table
    (conformance : RawJoinConstructionConformance compiled result)
    (node : compiled.val.NodeId) :
    result.plainFinal.val.nodes (conformance.nodeEquiv node) =
      (compiled.val.nodes node).rename conformance.regionEquiv := by
  have rawExact := result.plainNodeData_exact (conformance.nodeEquiv node)
  have compiledExact := conformance.nodeData node
  have originExact :
      result.finalNodeOriginEquiv (conformance.nodeEquiv node) =
        conformance.nodes node := by
    exact result.finalNodeOriginEquiv.apply_symm_apply _
  rw [originExact] at rawExact
  have same := rawExact.trans compiledExact.symm
  cases compiledData : compiled.val.nodes node with
  | atom compiledRegion compiledArgs =>
      cases rawData : result.plainFinal.val.nodes
          (conformance.nodeEquiv node) with
      | atom rawRegion rawArgs =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
          simp [compiledData, CNode.rename]
          exact ⟨(conformance.region_eq_originInverse_iff
            rawRegion compiledRegion).mpr same.1, same.2⟩
      | ref rawRegion definition rawArgs =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
      | identity rawRegion signature arity =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
  | ref compiledRegion compiledDefinition compiledArgs =>
      cases rawData : result.plainFinal.val.nodes
          (conformance.nodeEquiv node) with
      | atom rawRegion rawArgs =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
      | ref rawRegion rawDefinition rawArgs =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
          simp [compiledData, CNode.rename]
          exact ⟨(conformance.region_eq_originInverse_iff
            rawRegion compiledRegion).mpr same.1, same.2⟩
      | identity rawRegion signature arity =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
  | identity compiledRegion compiledSignature compiledArity =>
      cases rawData : result.plainFinal.val.nodes
          (conformance.nodeEquiv node) with
      | atom rawRegion rawArgs =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
      | ref rawRegion definition rawArgs =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
      | identity rawRegion rawSignature rawArity =>
          simp [ConcreteWireQuantifier.RelationJoinResult.plainNodeData,
            compiledNodeData, compiledData, rawData] at same
          simp [compiledData, CNode.rename]
          exact ⟨(conformance.region_eq_originInverse_iff
            rawRegion compiledRegion).mpr same.1, same.2⟩

private theorem wire_signature
    (conformance : RawJoinConstructionConformance compiled result)
    (wire : compiled.val.WireId) :
    (result.plainFinal.val.wires
      (conformance.wireEquiv wire)).sig =
        (compiled.val.wires wire).sig := by
  change (result.plainFinal.val.wires
      ((ConcreteWireQuantifier.finalWireOriginEquiv result).symm
        (conformance.wires wire))).sig =
    (compiled.val.wires wire).sig
  have rawExact := result.plainFinal_wire_signature_at_origin
    (conformance.wires wire)
  exact rawExact.trans (conformance.wireSignature wire).symm

private theorem wire_scope
    (conformance : RawJoinConstructionConformance compiled result)
    (wire : compiled.val.WireId) :
    (result.plainFinal.val.wires
      (conformance.wireEquiv wire)).scope =
        conformance.regionEquiv (compiled.val.wires wire).scope := by
  change (result.plainFinal.val.wires
      ((ConcreteWireQuantifier.finalWireOriginEquiv result).symm
        (conformance.wires wire))).scope =
    result.finalRegionOriginEquiv.symm
      (conformance.regions (compiled.val.wires wire).scope)
  apply result.finalRegionOriginEquiv.injective
  rw [result.finalRegionOriginEquiv.apply_symm_apply]
  have rawExact := result.plainFinal_wire_scope_at_origin
    (conformance.wires wire)
  exact rawExact.trans (conformance.wireScope wire).symm

private def endpointMap
    (conformance : RawJoinConstructionConformance compiled result)
    (endpoint : CEndpoint compiled.val.nodeCount) :
    CEndpoint result.plainFinal.val.nodeCount :=
  { node := conformance.nodeEquiv endpoint.node, port := endpoint.port }

private def endpointInverse
    (conformance : RawJoinConstructionConformance compiled result)
    (endpoint : CEndpoint result.plainFinal.val.nodeCount) :
    CEndpoint compiled.val.nodeCount :=
  { node := conformance.nodeEquiv.symm endpoint.node, port := endpoint.port }

@[simp]
private theorem endpointInverse_map
    (conformance : RawJoinConstructionConformance compiled result)
    (endpoint : CEndpoint compiled.val.nodeCount) :
    conformance.endpointInverse (conformance.endpointMap endpoint) =
      endpoint := by
  cases endpoint with
  | mk node port =>
      change CEndpoint.mk
          (conformance.nodeEquiv.symm (conformance.nodeEquiv node)) port =
        CEndpoint.mk node port
      exact congrArg (fun target => CEndpoint.mk target port)
        (conformance.nodeEquiv.left_inv node)

@[simp]
private theorem endpointMap_inverse
    (conformance : RawJoinConstructionConformance compiled result)
    (endpoint : CEndpoint result.plainFinal.val.nodeCount) :
    conformance.endpointMap (conformance.endpointInverse endpoint) =
      endpoint := by
  cases endpoint with
  | mk node port =>
      change CEndpoint.mk
          (conformance.nodeEquiv (conformance.nodeEquiv.symm node)) port =
        CEndpoint.mk node port
      exact congrArg (fun target => CEndpoint.mk target port)
        (conformance.nodeEquiv.right_inv node)

private theorem endpointMap_origin
    (conformance : RawJoinConstructionConformance compiled result)
    (endpoint : CEndpoint compiled.val.nodeCount) :
    result.finalEndpointOriginEquiv (conformance.endpointMap endpoint) =
      compiledEndpointOrigin compiled conformance.nodes endpoint := by
  cases endpoint with
  | mk node port =>
      apply congrArg (fun origin =>
        ({ node := origin, port := port } :
          ConcreteWireQuantifier.RawEndpoint
            (ConcreteWireQuantifier.RelationJoinResult.FinalNodeOrigin
              result)))
      exact result.finalNodeOriginEquiv.apply_symm_apply _

private theorem endpoint_mem_iff
    (conformance : RawJoinConstructionConformance compiled result)
    (wire : compiled.val.WireId)
    (endpoint : CEndpoint compiled.val.nodeCount) :
    endpoint ∈ (compiled.val.wires wire).endpoints ↔
      conformance.endpointMap endpoint ∈
        (result.plainFinal.val.wires
          (conformance.wireEquiv wire)).endpoints := by
  have classifiedLists :
      (compiled.val.wires wire).endpoints.map
          (compiledEndpointOrigin compiled conformance.nodes) =
        (result.plainFinal.val.wires
          (conformance.wireEquiv wire)).endpoints.map
            result.finalEndpointOriginEquiv := by
    calc
      _ = ConcreteWireQuantifier.expectedFinalWireEndpoints result
          (conformance.wires wire) := conformance.wireEndpoints wire
      _ = _ := by
        change _ = (result.plainFinal.val.wires
          ((ConcreteWireQuantifier.finalWireOriginEquiv result).symm
            (conformance.wires wire))).endpoints.map
              result.finalEndpointOriginEquiv
        exact (result.finalWire_endpoints_exact
          (conformance.wires wire)).symm
  constructor
  · intro member
    have classifiedMember :
        compiledEndpointOrigin compiled conformance.nodes endpoint ∈
          (compiled.val.wires wire).endpoints.map
            (compiledEndpointOrigin compiled conformance.nodes) :=
      List.mem_map.mpr ⟨endpoint, member, rfl⟩
    rw [classifiedLists] at classifiedMember
    rcases List.mem_map.mp classifiedMember with
      ⟨candidate, candidateMember, candidateOrigin⟩
    have candidateExact : candidate = conformance.endpointMap endpoint := by
      apply result.finalEndpointOriginEquiv.injective
      exact candidateOrigin.trans (conformance.endpointMap_origin endpoint).symm
    simpa only [candidateExact] using candidateMember
  · intro member
    have classifiedMember :
        result.finalEndpointOriginEquiv
            (conformance.endpointMap endpoint) ∈
          (result.plainFinal.val.wires
            (conformance.wireEquiv wire)).endpoints.map
              result.finalEndpointOriginEquiv :=
      List.mem_map.mpr ⟨conformance.endpointMap endpoint, member, rfl⟩
    rw [← classifiedLists] at classifiedMember
    rw [conformance.endpointMap_origin endpoint] at classifiedMember
    rcases List.mem_map.mp classifiedMember with
      ⟨candidate, candidateMember, candidateOrigin⟩
    have candidateExact : candidate = endpoint := by
      rcases candidate with ⟨candidateNode, candidatePort⟩
      rcases endpoint with ⟨endpointNode, endpointPort⟩
      simp [compiledEndpointOrigin] at candidateOrigin
      rcases candidateOrigin with ⟨nodeExact, portExact⟩
      subst candidatePort
      exact congrArg (fun target => CEndpoint.mk target endpointPort)
        (conformance.nodes.injective nodeExact)
    simpa only [candidateExact] using candidateMember

private theorem endpointMap_corresponds
    (conformance : RawJoinConstructionConformance compiled result)
    (wire : compiled.val.WireId)
    (endpoint : CEndpoint compiled.val.nodeCount)
    (member : endpoint ∈ (compiled.val.wires wire).endpoints) :
    PortCorresponds compiled.val result.plainFinal.val
      conformance.nodeEquiv endpoint (conformance.endpointMap endpoint) := by
  rcases endpoint with ⟨endpointNode, endpointPort⟩
  refine ⟨rfl, ?_⟩
  have required := ConcreteDiagram.incident_port_required _
    compiled.val compiled.property wire ⟨endpointNode, endpointPort⟩ member
  unfold endpointMap
  dsimp only [CEndpoint.node, CEndpoint.port]
  rw [conformance.node_table endpointNode]
  rw [CNode.rename_eq_relocate]
  cases nodeData : compiled.val.nodes endpointNode with
  | atom region args => rfl
  | ref region definition args => rfl
  | identity region signature arity =>
      have identityRequired :
          endpointPort ∈ (List.range arity).map CPort.identity := by
        simpa [ConcreteDiagram.requiredPorts, nodeData] using required
      obtain ⟨index, _, portExact⟩ := List.mem_map.mp identityRequired
      exact ⟨rfl, rfl, index, index, portExact.symm, portExact.symm⟩

private def endpointFiber
    (conformance : RawJoinConstructionConformance compiled result)
    (wire : compiled.val.WireId) :
    ConcreteIso.EndpointFiberEquiv conformance.nodeEquiv
      conformance.wireEquiv wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨conformance.endpointMap endpoint.1,
          (conformance.endpoint_mem_iff wire endpoint.1).mp endpoint.2⟩
      invFun := fun candidate =>
        ⟨conformance.endpointInverse candidate.1, by
          apply (conformance.endpoint_mem_iff wire
            (conformance.endpointInverse candidate.1)).mpr
          simpa using candidate.2⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact conformance.endpointInverse_map endpoint.1
      right_inv := by
        intro candidate
        apply Subtype.ext
        exact conformance.endpointMap_inverse candidate.1 }
  corresponds := by
    intro endpoint
    exact conformance.endpointMap_corresponds wire endpoint.1 endpoint.2

/-- Assemble the primitive/raw landing directly from construction-owned
terminal origin tables. -/
private def constructionIso
    (conformance : RawJoinConstructionConformance compiled result) :
    ConcreteIso compiled.val result.plainFinal.val :=
  ConcreteIso.ofEquivs conformance.regionEquiv conformance.nodeEquiv
    conformance.wireEquiv conformance.root_exact conformance.region_table
    conformance.node_table conformance.wire_signature conformance.wire_scope
    conformance.endpointFiber

end RawJoinConstructionConformance

/-- The primitive construction of a raw accepted relation join. -/
private structure RawRelationJoinCompilation
    (orientation : Orientation)
    (source rawTarget : CheckedDiagram definitions) where
  program : PrimitiveProgram orientation source
  remainingTracked : List program.target.val.WireId
  trackedEmpty : remainingTracked = []
  constructionIso : ConcreteIso program.target.val rawTarget.val

private def compileRawRelationJoinResidual
    (source : CheckedDiagram definitions)
    (rawTarget : CheckedDiagram definitions)
    (residual : IntrinsicCompilerResidual source context)
    (orientation : Orientation) :
    Except CompilerError
      (RawRelationJoinCompilation orientation source rawTarget) := do
  let compiled ← compileResidual residual [] orientation
  have trackedEmpty : compiled.tracked = [] :=
    List.eq_nil_of_length_eq_zero compiled.trackedLength
  let constructionLanding ←
    requireOption .redundancyMismatch <|
      ConcreteIsoSearch.findConcreteIso?
        compiled.construction.1.val rawTarget.val
  let compiled := compiled.retarget rawTarget constructionLanding
  pure
    { program := compiled.program
      remainingTracked := compiled.tracked
      trackedEmpty := trackedEmpty
      constructionIso := compiled.construction.2 }

/-- A successful join compilation and its independently checked redundancy. -/
structure CompiledRelationJoin
    {source : CheckedDiagram definitions}
    (input : MonolithicRelationJoinInput source) where
  monolithic : AcceptedMonolithicRelationJoin source input
  arguments : List Sig
  sourceSignature : (source.val.wires input.wire).sig = .rel arguments
  boundary : JoinBoundaryReceipt input arguments
  program : PrimitiveProgram input.orientation source
  remainingTracked : List program.target.val.WireId
  trackedEmpty : remainingTracked = []
  constructionIso :
    ConcreteIso program.target.val monolithic.plainFinal.val

/-- A successful sever compilation and its independently checked redundancy. -/
structure CompiledRelationSever
    {source : CheckedDiagram definitions}
    (input : MonolithicRelationSeverInput source) where
  monolithic : AppliedMonolithicRelationSever source input
  program : PrimitiveProgram input.orientation source
  constructionIso :
    ConcreteIso program.target.val monolithic.target.val

namespace CompiledRelationJoin

/-- Transport any ordered final boundary through the raw construction
isomorphism. `List.map` preserves positions and repeated aliases. -/
def transportBoundary
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (compiled : CompiledRelationJoin input)
    (boundary : List compiled.program.target.val.WireId) :
    List compiled.monolithic.plainFinal.val.WireId :=
  boundary.map compiled.constructionIso.wires

@[simp]
theorem transportBoundary_length
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (compiled : CompiledRelationJoin input)
    (boundary : List compiled.program.target.val.WireId) :
    (compiled.transportBoundary boundary).length = boundary.length := by
  simp [transportBoundary]

@[simp]
theorem transportBoundary_get
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (compiled : CompiledRelationJoin input)
    (boundary : List compiled.program.target.val.WireId)
    (position : Fin boundary.length) :
    (compiled.transportBoundary boundary).get
        (Fin.cast (compiled.transportBoundary_length boundary).symm position) =
      compiled.constructionIso.wires (boundary.get position) := by
  simp [transportBoundary]

end CompiledRelationJoin

namespace CompiledRelationSever

/-- Exact ordered boundary transport for a reversed sever program. -/
def transportBoundary
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (compiled : CompiledRelationSever input)
    (boundary : List compiled.program.target.val.WireId) :
    List compiled.monolithic.target.val.WireId :=
  boundary.map compiled.constructionIso.wires

@[simp]
theorem transportBoundary_length
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (compiled : CompiledRelationSever input)
    (boundary : List compiled.program.target.val.WireId) :
    (compiled.transportBoundary boundary).length = boundary.length := by
  simp [transportBoundary]

@[simp]
theorem transportBoundary_get
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (compiled : CompiledRelationSever input)
    (boundary : List compiled.program.target.val.WireId)
    (position : Fin boundary.length) :
    (compiled.transportBoundary boundary).get
        (Fin.cast (compiled.transportBoundary_length boundary).symm position) =
      compiled.constructionIso.wires (boundary.get position) := by
  simp [transportBoundary]

end CompiledRelationSever

private def compileAppliedRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source)
    (monolithic : AcceptedMonolithicRelationJoin source input) :
    Except CompilerError (CompiledRelationJoin input) := do
  let arguments := monolithic.arguments
  let sourceSignature := monolithic.sourceSignature
  let boundary : JoinBoundaryReceipt input arguments :=
    { marker := ()
      boundaryLength := monolithic.boundaryLength
      formalSignatures := monolithic.formalSignatures
      parameterSignatures := monolithic.parameterSignatures }
  let residual := initialIntrinsicResidual monolithic
  let compiled ←
    compileRawRelationJoinResidual source monolithic.plainFinal residual
      input.orientation
  pure
    { monolithic := monolithic
      arguments := arguments
      sourceSignature := sourceSignature
      boundary := boundary
      program := compiled.program
      remainingTracked := compiled.remainingTracked
      trackedEmpty := compiled.trackedEmpty
      constructionIso := compiled.constructionIso }

/--
Compile one accepted strongest-form relation join into the checked primitive
language.  The recursion bound is derived internally from the residual and is
not part of the public interface; `CompilerTermination` supplies the
well-founded structural order used by the final recursion.
-/
def compileRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source) :
    Except CompilerError (CompiledRelationJoin input) := do
  let monolithic ←
    (applyAcceptedMonolithicRelationJoin source input).mapError
      .monolithicJoinRejected
  compileAppliedRelationJoin source input monolithic

/--
The sever compiler is implemented below by compiling the checked virtual
inverse join and reversing its checked receipt chain.
-/
def compileRelationSever
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationSeverInput source) :
    Except CompilerError (CompiledRelationSever input) := do
  let monolithic ←
    (applyMonolithicRelationSever source input).mapError
      .monolithicSeverRejected
  let receipt := monolithic.concreteReceipt
  let inverseInput := monolithic.inverseJoinInput
  let residual :=
    initialRawIntrinsicResidual (input := inverseInput)
      receipt.inverseChecked receipt.inverse
  let planned ←
    compileRawRelationJoinResidual receipt.result.checked
      receipt.inverse.plainFinal residual inverseInput.orientation
  let reconstruction ←
    requireOption .redundancyMismatch <|
      ConcreteIsoSearch.findConcreteIso?
        planned.program.target.val source.val
  let reversed ←
    reversePrimitiveProgram planned.program source reconstruction
      input.orientation
  let targetIso :
      ConcreteIso receipt.result.checked.val monolithic.target.val := by
    exact checkedDiagramEqIso receipt.targetExact.symm
  pure
    { monolithic := monolithic
      program := reversed.program
      constructionIso := reversed.constructionIso.trans targetIso }

end WirePrimitive

end VisualProof
