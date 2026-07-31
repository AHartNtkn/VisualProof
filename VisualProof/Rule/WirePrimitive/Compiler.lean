import VisualProof.Rule.WirePrimitive.CompilerTermination
import VisualProof.Rule.MonolithicWireQuantifier
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
  | vacuousRejected (error : StructuralCore.StructuralError)
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
noncomputable def initialIntrinsicResidual
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (monolithic : AppliedMonolithicRelationJoin source input) :
    IntrinsicCompilerResidual source
      (ConcreteElaboration.openBoundaryClassSigs input.content.val) :=
  IntrinsicCompilerResidual.initial monolithic.contentCompilation
    input.wire monolithic.arguments monolithic.sourceSignature
    monolithic.sourceSites input.parameters
    (by simpa [checkedBoundarySigs] using monolithic.formalSignatures)
    (by simpa [checkedBoundarySigs] using monolithic.parameterSignatures)
    monolithic.live_not_parameter

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
        ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
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
              ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate,
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
          let vacuousStep :
              CompiledPrimitiveStep orientation deleteStep.target :=
            .vacuousElim vacuousInput vacuous
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

private def initialContentResidual
    (content : CheckedOpenDiagram definitions)
    (compilation : OpenCompilation content)
    (formals : Nat) :
    ContentResidual content where
  compilation := compilation
  root := content.val.diagram.root
  regions := content.val.diagram.regionsList
  nodes := content.val.diagram.nodesList
  wires := content.val.diagram.wiresList
  boundary := content.val.boundary
  formals := formals

private def promoteBinder
    (residual : ContentResidual content)
    (binder : content.val.diagram.WireId) :
    ContentResidual content where
  compilation := residual.compilation
  root := residual.root
  regions := residual.regions
  nodes := residual.nodes
  wires := residual.wires
  boundary :=
    residual.boundary.take residual.formals ++
      [binder] ++ residual.boundary.drop residual.formals
  formals := residual.formals + 1

private def subtreeRegions
    (residual : ContentResidual content)
    (root : content.val.diagram.RegionId) :
    List content.val.diagram.RegionId :=
  residual.regions.filter fun region =>
    decide (content.val.diagram.Encloses root region)

private def boundaryOrScopedIn
    (residual : ContentResidual content)
    (regions : List content.val.diagram.RegionId)
    (wire : content.val.diagram.WireId) : Bool :=
  decide (
    wire ∈ residual.boundary ∨
      (content.val.diagram.wires wire).scope ∈ regions)

private def onlyRootNode
    (residual : ContentResidual content)
    (node : content.val.diagram.NodeId) :
    ContentResidual content where
  compilation := residual.compilation
  root := residual.root
  regions := [residual.root]
  nodes := [node]
  wires :=
    residual.wires.filter fun wire =>
      decide (wire ∈ residual.boundary)
  boundary := residual.boundary
  formals := residual.formals

private def withoutRootNode
    (residual : ContentResidual content)
    (node : content.val.diagram.NodeId) :
    ContentResidual content where
  compilation := residual.compilation
  root := residual.root
  regions := residual.regions
  nodes := residual.nodes.filter fun candidate => decide (candidate ≠ node)
  wires :=
    residual.wires.filter fun wire =>
      decide (
        wire ∈ residual.boundary ∨
          (content.val.diagram.wires wire).scope ≠ residual.root)
  boundary := residual.boundary
  formals := residual.formals

private def onlyRootCut
    (residual : ContentResidual content)
    (cut : content.val.diagram.RegionId) :
    ContentResidual content :=
  let subtree := subtreeRegions residual cut
  { compilation := residual.compilation
    root := residual.root
    regions := residual.root :: subtree
    nodes :=
      residual.nodes.filter fun node =>
        decide ((content.val.diagram.nodes node).region ∈ subtree)
    wires :=
      residual.wires.filter fun wire =>
        boundaryOrScopedIn residual subtree wire
    boundary := residual.boundary
    formals := residual.formals }

private def withoutRootCut
    (residual : ContentResidual content)
    (cut : content.val.diagram.RegionId) :
    ContentResidual content :=
  let subtree := subtreeRegions residual cut
  let retainedRegions :=
    residual.regions.filter fun region => decide (region ∉ subtree)
  { compilation := residual.compilation
    root := residual.root
    regions := retainedRegions
    nodes :=
      residual.nodes.filter fun node =>
        decide ((content.val.diagram.nodes node).region ∉ subtree)
    wires :=
      residual.wires.filter fun wire =>
        boundaryOrScopedIn residual retainedRegions wire
    boundary := residual.boundary
    formals := residual.formals }

private def insideRootCut
    (residual : ContentResidual content)
    (cut : content.val.diagram.RegionId) :
    ContentResidual content :=
  let subtree := subtreeRegions residual cut
  { compilation := residual.compilation
    root := cut
    regions := subtree
    nodes :=
      residual.nodes.filter fun node =>
        decide ((content.val.diagram.nodes node).region ∈ subtree)
    wires :=
      residual.wires.filter fun wire =>
        boundaryOrScopedIn residual subtree wire
    boundary := residual.boundary
    formals := residual.formals }

private def ambientLookup?
    {content : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (ambients :
      List (content.val.diagram.WireId × source.val.WireId))
    (stub : content.val.diagram.WireId) :
    Option source.val.WireId :=
  (ambients.find? fun pair => decide (pair.1 = stub)).map Prod.snd

private def portOwner?
    (content : CheckedOpenDiagram definitions)
    (node : content.val.diagram.NodeId)
    (port : CPort) :
    Option content.val.diagram.WireId :=
  content.val.diagram.endpointOwner? ⟨node, port⟩

private def argumentOwners?
    (content : CheckedOpenDiagram definitions)
    (node : content.val.diagram.NodeId)
    (kind : Nat → CPort)
    (arity : Nat) :
    Option (List content.val.diagram.WireId) :=
  (List.range arity).mapM fun position =>
    portOwner? content node (kind position)

private structure TransportState
    (content : CheckedOpenDiagram definitions)
    (target : CheckedDiagram definitions)
    (trackedCount : Nat) where
  tracked : List target.val.WireId
  trackedLength : tracked.length = trackedCount
  ambients :
    List (content.val.diagram.WireId × target.val.WireId)

private def unpackTransport?
    {content : CheckedOpenDiagram definitions}
    {target : CheckedDiagram definitions}
    (ambientStubs : List content.val.diagram.WireId)
    (trackedCount : Nat)
    (mapped : List target.val.WireId) :
    Option (TransportState content target trackedCount) := by
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
    {content : CheckedOpenDiagram definitions}
    {source : CheckedDiagram definitions}
    (tracked : List source.val.WireId)
    (ambients :
      List (content.val.diagram.WireId × source.val.WireId)) :
    List source.val.WireId :=
  tracked ++ ambients.map Prod.snd

private structure ResidualCompilation
    (orientation : Orientation)
    (source : CheckedDiagram definitions)
    (content : CheckedOpenDiagram definitions)
    (trackedCount : Nat) where
  program : PrimitiveProgram orientation source
  tracked : List program.target.val.WireId
  trackedLength : tracked.length = trackedCount
  ambients :
    List (content.val.diagram.WireId × program.target.val.WireId)

namespace ResidualCompilation

private def castTracked
    (compiled :
      ResidualCompilation orientation source content currentCount)
    (exact : currentCount = targetCount) :
    ResidualCompilation orientation source content targetCount where
  program := compiled.program
  tracked := compiled.tracked
  trackedLength := compiled.trackedLength.trans exact
  ambients := compiled.ambients

private def prepend
    {source : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep orientation source)
    (tail :
      ResidualCompilation orientation step.target content trackedCount) :
    ResidualCompilation orientation source content trackedCount where
  program := .cons step tail.program
  tracked := tail.tracked
  trackedLength := tail.trackedLength
  ambients := tail.ambients

end ResidualCompilation

private def combineParallel
    {source : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep orientation source)
    (leftProgram : PrimitiveProgram orientation step.target)
    (right :
      ResidualCompilation orientation leftProgram.target content currentCount)
    (countExact : currentCount = targetCount) :
    ResidualCompilation orientation source content targetCount := by
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
        exact right'.ambients }

private def terminalCompilation
    (content : CheckedOpenDiagram definitions)
    (trackedCount : Nat)
    (ambientStubs : List content.val.diagram.WireId)
    (terminal : TerminalStepRun orientation source
      (trackedCount + ambientStubs.length)) :
    Except CompilerError
      (ResidualCompilation orientation source content trackedCount) := do
  let transported ←
    requireOption .allocationMismatch <|
      unpackTransport? ambientStubs trackedCount terminal.tracked
  pure
    { program := .cons terminal.step (.nil terminal.step.target)
      tracked := transported.tracked
      trackedLength := transported.trackedLength
      ambients := transported.ambients }

private def primitiveCompilation
    (content : CheckedOpenDiagram definitions)
    (trackedCount : Nat)
    (ambientStubs : List content.val.diagram.WireId)
    (run : PrimitiveRun orientation source
      (trackedCount + ambientStubs.length)) :
    Except CompilerError
      (ResidualCompilation orientation source content trackedCount) := do
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
    (content : CheckedOpenDiagram definitions)
  | extend (stub : content.val.diagram.WireId) (position : Nat)
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
    (content : CheckedOpenDiagram definitions) where
  positions : List content.val.diagram.WireId
  operations : List (PlumbingOp content)

private def materializePlan
    (content : CheckedOpenDiagram definitions)
    (initial target : List content.val.diagram.WireId) :
    PlumbingPlan content :=
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
    (target : List content.val.diagram.WireId)
    (initial : PlumbingPlan content) :
    PlumbingPlan content :=
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
    (target : List content.val.diagram.WireId)
    (plan : PlumbingPlan content)
    (position : Nat) :
    Option (PlumbingPlan content) := do
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
          let afterDuplicate : PlumbingPlan content :=
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
        let afterDuplicate : PlumbingPlan content :=
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
    (target : List content.val.diagram.WireId)
    (initial : PlumbingPlan content) :
    Option (PlumbingPlan content) :=
  (List.range target.length).foldlM (arrangeOne target) initial

/--
Plan exact tuple normalization solely from content identifiers.  The
primitive checkers subsequently validate every emitted operation against the
live host diagram.
-/
private def planPlumbing
    (content : CheckedOpenDiagram definitions)
    (initial target : List content.val.diagram.WireId) :
    Option (List (PlumbingOp content)) := do
  let materialized := materializePlan content initial target
  let dropped := dropUnusedPlan target materialized
  let arranged ← arrangePlan target dropped
  if arranged.positions = target then
    pure arranged.operations
  else
    none

private structure LiveResidualCompilation
    (orientation : Orientation)
    (source : CheckedDiagram definitions)
    (content : CheckedOpenDiagram definitions)
    (trackedCount : Nat) where
  program : PrimitiveProgram orientation source
  live : program.target.val.WireId
  tracked : List program.target.val.WireId
  trackedLength : tracked.length = trackedCount
  ambients :
    List (content.val.diagram.WireId × program.target.val.WireId)

namespace LiveResidualCompilation

private def castTracked
    (compiled :
      LiveResidualCompilation orientation source content currentCount)
    (exact : currentCount = targetCount) :
    LiveResidualCompilation orientation source content targetCount where
  program := compiled.program
  live := compiled.live
  tracked := compiled.tracked
  trackedLength := compiled.trackedLength.trans exact
  ambients := compiled.ambients

private def prepend
    {source : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep orientation source)
    (tail :
      LiveResidualCompilation orientation step.target content trackedCount) :
    LiveResidualCompilation orientation source content trackedCount where
  program := .cons step tail.program
  live := tail.live
  tracked := tail.tracked
  trackedLength := tail.trackedLength
  ambients := tail.ambients

end LiveResidualCompilation

private def executePlumbing
    {definitions : List (List Sig)}
    {content : CheckedOpenDiagram definitions} :
    (operations : List (PlumbingOp content)) →
    (source : CheckedDiagram definitions) →
    (wire : source.val.WireId) →
    (ambients :
      List (content.val.diagram.WireId × source.val.WireId)) →
    (tracked : List source.val.WireId) →
    (orientation : Orientation) →
    Except CompilerError
      (LiveResidualCompilation orientation source content tracked.length)
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
              (content.val.diagram.wires stub).sig attachment orientation packed
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
    (content : CheckedOpenDiagram definitions)
    (plumbed :
      LiveResidualCompilation orientation source content trackedCount)
    (terminal :
      TerminalStepRun orientation plumbed.program.target
        (plumbed.tracked.length + plumbed.ambients.length)) :
    Except CompilerError
      (ResidualCompilation orientation source content trackedCount) := do
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

private def compileLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (residual : ContentResidual content)
    (node : content.val.diagram.NodeId)
    (ambients :
      List (content.val.diagram.WireId × source.val.WireId))
    (tracked : List source.val.WireId)
    (orientation : Orientation) :
    Except CompilerError
      (ResidualCompilation orientation source content tracked.length) := do
  let positions := residual.boundary.take residual.formals
  match content.val.diagram.nodes node with
  | .atom _ signatures =>
      let head ←
        requireOption .malformedResidual <|
          portOwner? content node .head
      let arguments ←
        requireOption .malformedResidual <|
          argumentOwners? content node CPort.arg signatures.length
      if formal : head ∈ positions then
        let operations ←
          requireOption .malformedResidual <|
            planPlumbing content positions (head :: arguments)
        let plumbed ←
          executePlumbing operations source wire ambients tracked orientation
        let packed := packedTracked plumbed.tracked plumbed.ambients
        let terminal ←
          runApplyFormal plumbed.program.target plumbed.live 0 orientation
            packed
        finishPlumbed content plumbed
          (by
            simpa [packed, packedTracked] using terminal)
      else
        let fixed ←
          requireOption .missingAmbient <|
            ambientLookup? ambients head
        let operations ←
          requireOption .malformedResidual <|
            planPlumbing content positions arguments
        let plumbed ←
          executePlumbing operations source wire ambients tracked orientation
        let fixed' ←
          requireOption .missingAmbient <|
            ambientLookup? plumbed.ambients head
        let packed := packedTracked plumbed.tracked plumbed.ambients
        let terminal ←
          runWireJoin plumbed.program.target fixed' plumbed.live orientation
            packed
        finishPlumbed content plumbed
          (by
            simpa [packed, packedTracked] using terminal)
  | .ref _ definition signatures =>
      let arguments ←
        requireOption .malformedResidual <|
          argumentOwners? content node CPort.arg signatures.length
      let operations ←
        requireOption .malformedResidual <|
          planPlumbing content positions arguments
      let plumbed ←
        executePlumbing operations source wire ambients tracked orientation
      let packed := packedTracked plumbed.tracked plumbed.ambients
      let terminal ←
        runRefLeaf plumbed.program.target plumbed.live definition orientation
          packed
      finishPlumbed content plumbed
        (by
          simpa [packed, packedTracked] using terminal)
  | .identity _ _ arity =>
      let arguments ←
        requireOption .malformedResidual <|
          argumentOwners? content node CPort.identity arity
      let operations ←
        requireOption .malformedResidual <|
          planPlumbing content positions arguments
      let plumbed ←
        executePlumbing operations source wire ambients tracked orientation
      let packed := packedTracked plumbed.tracked plumbed.ambients
      let terminal ←
        runIdentityLeaf plumbed.program.target plumbed.live orientation packed
      finishPlumbed content plumbed
        (by
          simpa [packed, packedTracked] using terminal)

private def compileResidual
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (residual : ContentResidual content)
    (ambients :
      List (content.val.diagram.WireId × source.val.WireId))
    (tracked : List source.val.WireId)
    (orientation : Orientation) :
    Except CompilerError
      (ResidualCompilation orientation source content tracked.length) := do
      let ambientStubs := ambients.map Prod.fst
      let packed := packedTracked tracked ambients
      match residual.internalRootWires with
      | binder :: _ =>
          let shifted ←
            runArityShift source wire
              (content.val.diagram.wires binder).sig orientation packed
          let transported ←
            requireOption .allocationMismatch <|
              unpackTransport? ambientStubs tracked.length shifted.tracked
          let nextResidual := promoteBinder residual binder
          if smaller :
              ContentResidual.Before nextResidual.measure residual.measure then
            let tail ←
              compileResidual shifted.step.target shifted.live content
                nextResidual transported.ambients transported.tracked
                orientation
            pure
              ((tail.castTracked transported.trackedLength).prepend
                shifted.step)
          else
            throw .malformedResidual
      | [] =>
          let nodes := residual.rootNodes
          let cuts := residual.rootCuts
          match nodes, cuts with
          | [], [] =>
              let emptied ←
                runEmptyResidual source wire orientation packed
              primitiveCompilation content tracked.length ambientStubs
                (by
                  simpa [packed, packedTracked, ambientStubs] using emptied)
          | [node], [] =>
              compileLeaf source wire content residual node ambients
                tracked orientation
          | [], [cut] =>
              let wrapped ← runCutWrap source wire orientation packed
              let transported ←
                requireOption .allocationMismatch <|
                  unpackTransport? ambientStubs tracked.length wrapped.tracked
              let nextResidual := insideRootCut residual cut
              if smaller :
                  ContentResidual.Before nextResidual.measure
                    residual.measure then
                let tail ←
                  compileResidual wrapped.step.target wrapped.live content
                    nextResidual transported.ambients transported.tracked
                    orientation
                pure
                  ((tail.castTracked transported.trackedLength).prepend
                    wrapped.step)
              else
                throw .malformedResidual
          | node :: _ :: _, _ =>
              let split ←
                runParallelSplit source wire orientation packed
              let transported ←
                requireOption .allocationMismatch <|
                  unpackTransport? ambientStubs tracked.length split.tracked
              let leftResidual := onlyRootNode residual node
              let rightResidual := withoutRootNode residual node
              if leftSmaller :
                  ContentResidual.Before leftResidual.measure
                    residual.measure then
                let left ←
                  compileResidual split.step.target split.left content
                    leftResidual transported.ambients
                    (split.right :: transported.tracked) orientation
                match rightSplit : left.tracked with
                | [] => throw .allocationMismatch
                | right :: remainingTracked =>
                    if rightSmaller :
                        ContentResidual.Before rightResidual.measure
                          residual.measure then
                      let rightCompiled ←
                        compileResidual left.program.target right content
                          rightResidual left.ambients remainingTracked
                          orientation
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
                    else
                      throw .malformedResidual
              else
                throw .malformedResidual
          | node :: _, _ :: _ =>
              let split ←
                runParallelSplit source wire orientation packed
              let transported ←
                requireOption .allocationMismatch <|
                  unpackTransport? ambientStubs tracked.length split.tracked
              let leftResidual := onlyRootNode residual node
              let rightResidual := withoutRootNode residual node
              if leftSmaller :
                  ContentResidual.Before leftResidual.measure
                    residual.measure then
                let left ←
                  compileResidual split.step.target split.left content
                    leftResidual transported.ambients
                    (split.right :: transported.tracked) orientation
                match rightSplit : left.tracked with
                | [] => throw .allocationMismatch
                | right :: remainingTracked =>
                    if rightSmaller :
                        ContentResidual.Before rightResidual.measure
                          residual.measure then
                      let rightCompiled ←
                        compileResidual left.program.target right content
                          rightResidual left.ambients remainingTracked
                          orientation
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
                    else
                      throw .malformedResidual
              else
                throw .malformedResidual
          | [], cut :: _ :: _ =>
              let split ←
                runParallelSplit source wire orientation packed
              let transported ←
                requireOption .allocationMismatch <|
                  unpackTransport? ambientStubs tracked.length split.tracked
              let leftResidual := onlyRootCut residual cut
              let rightResidual := withoutRootCut residual cut
              if leftSmaller :
                  ContentResidual.Before leftResidual.measure
                    residual.measure then
                let left ←
                  compileResidual split.step.target split.left content
                    leftResidual transported.ambients
                    (split.right :: transported.tracked) orientation
                match rightSplit : left.tracked with
                | [] => throw .allocationMismatch
                | right :: remainingTracked =>
                    if rightSmaller :
                        ContentResidual.Before rightResidual.measure
                          residual.measure then
                      let rightCompiled ←
                        compileResidual left.program.target right content
                          rightResidual left.ambients remainingTracked
                          orientation
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
                    else
                      throw .malformedResidual
              else
                throw .malformedResidual
termination_by residual.measure
decreasing_by
  all_goals assumption

private def subsets : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      let rest := subsets tail
      rest ++ rest.map (head :: ·)

private def tuples (length : Nat) (values : List α) : List (List α) :=
  match length with
  | 0 => [[]]
  | length + 1 =>
      values.flatMap fun head =>
        (tuples length values).map (head :: ·)

private def insertEverywhere (value : α) : List α → List (List α)
  | [] => [[value]]
  | head :: tail =>
      (value :: head :: tail) ::
        (insertEverywhere value tail).map (head :: ·)

private def permutations : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      (permutations tail).flatMap (insertEverywhere head)

private structure InverseStepRun
    (orientation : Orientation)
    (real planned : CheckedDiagram definitions) where
  step : CompiledPrimitiveStep orientation real
  normalizedIso : ConcreteIso step.target.val planned.val

private def selectInverse?
    (planned : CheckedDiagram definitions)
    (candidates : List (CompiledPrimitiveStep orientation real)) :
    Option (InverseStepRun orientation real planned) :=
  candidates.findSome? fun step =>
    (ConcreteIsoSearch.findConcreteIso? step.target.val planned.val).map
      fun normalizedIso => ⟨step, normalizedIso⟩

private def vacuousBoundCandidate
    (plain : CheckedDiagram definitions)
    (site : plain.val.RegionId)
    (signature : Sig) :
    ConcreteDiagram definitions.length where
  regionCount := plain.val.regionCount
  nodeCount := plain.val.nodeCount
  wireCount := plain.val.wireCount + 1
  root := plain.val.root
  regions := plain.val.regions
  nodes := plain.val.nodes
  wires :=
    Fin.addCases plain.val.wires fun _ =>
      { sig := signature
        scope := site
        endpoints := [] }

private def vacuousIntroCandidates
    (real : CheckedDiagram definitions)
    (signature : Sig)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.regionsList.filterMap fun site =>
    let candidate := vacuousBoundCandidate real site signature
    match _accepted :
        ConcreteDiagram.checkWellFormed definitions candidate with
    | .error _ => none
    | .ok bound =>
        let input : StructuralCore.VacuousInput real bound :=
          { site := site, sig := signature }
        match StructuralCore.checkVacuous input with
        | .error _ => none
        | .ok checked => some (.vacuousIntro input checked)

private def endSiteCandidates
    (real : CheckedDiagram definitions)
    (wire : real.val.WireId) :
    List (ConcreteWirePrimitive.EndSite real wire) :=
  match (real.val.wires wire).sig with
  | .iota => []
  | .rel arguments =>
      real.val.regionsList.flatMap fun region =>
        (tuples arguments.length real.val.wiresList).map fun attachments =>
          { region := region
            arguments := attachments }

private def endsSpawnCandidates
    (real : CheckedDiagram definitions)
    (siteCount : Nat)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun wire =>
    (tuples siteCount (endSiteCandidates real wire)).filterMap fun sites =>
      match applyEndsSpawn real wire sites orientation with
      | .error _ => none
      | .ok applied => some (.endsSpawn wire sites applied)

private def abstractFormalCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.regionsList.flatMap fun scope =>
    (subsets real.val.nodesList).filterMap fun nodes =>
      match Leaves.applyAbstractFormal real nodes scope orientation with
      | .error _ => none
      | .ok applied => some (.abstractFormal nodes scope applied)

private def identityAbstractCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.regionsList.flatMap fun scope =>
    (subsets real.val.nodesList).filterMap fun nodes =>
      match Leaves.applyIdentityAbstract real nodes scope orientation with
      | .error _ => none
      | .ok applied => some (.identityAbstract nodes scope applied)

private def refAbstractCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.regionsList.flatMap fun scope =>
    (subsets real.val.nodesList).filterMap fun nodes =>
      match Leaves.applyRefAbstract real nodes scope orientation with
      | .error _ => none
      | .ok applied => some (.refAbstract nodes scope applied)

private def wireSeverCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun wire =>
    real.val.regionsList.flatMap fun scope =>
      (subsets (real.val.wires wire).endpoints).filterMap fun keep =>
        let input : WireSeverInput real :=
          { orientation := orientation
            wire := wire
            keep := keep
            scope := scope }
        match applyWireSever real input with
        | .error _ => none
        | .ok applied => some (.wireSever input rfl applied)

private def wireJoinCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun left =>
    real.val.wiresList.filterMap fun right =>
      let input : WireJoinInput real :=
        { orientation := orientation
          left := left
          right := right }
      match applyWireJoin real input with
      | .error _ => none
      | .ok applied => some (.wireJoin input rfl applied)

private def cutAbsorbCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.filterMap fun wire =>
    match applyCutAbsorb real wire with
    | .error _ => none
    | .ok applied => some (.cutAbsorb wire applied)

private def cutWrapCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.filterMap fun wire =>
    match applyCutWrap real wire with
    | .error _ => none
    | .ok applied => some (.cutWrap wire applied)

private def parallelFuseCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun left =>
    real.val.wiresList.filterMap fun right =>
      match applyParallelFuse real left right with
      | .error _ => none
      | .ok applied => some (.parallelFuse left right applied)

private def parallelSplitCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.filterMap fun wire =>
    match applyParallelSplit real wire with
    | .error _ => none
    | .ok applied => some (.parallelSplit wire applied)

private def arityUnshiftCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun wire =>
    match (real.val.wires wire).sig with
    | .iota => []
    | .rel arguments =>
        (List.range arguments.length).filterMap fun position =>
          match applyArityUnshift real wire position with
          | .error _ => none
          | .ok applied => some (.arityUnshift wire position applied)

private def argDropCandidates
    (real : CheckedDiagram definitions)
    (position : Nat)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.filterMap fun wire =>
    match applyArgDrop real wire position orientation with
    | .error _ => none
    | .ok applied => some (.argDrop wire position applied)

private def argExtendCandidates
    (real : CheckedDiagram definitions)
    (position : Nat)
    (newArgument : Sig)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun wire =>
    (tuples (real.val.wires wire).endpoints.length
        real.val.wiresList).filterMap fun attachments =>
      match
          applyArgExtend real wire position newArgument attachments orientation
      with
      | .error _ => none
      | .ok applied =>
          some
            (.argExtend wire position newArgument attachments applied)

private def argPermuteCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun wire =>
    match (real.val.wires wire).sig with
    | .iota => []
    | .rel arguments =>
        (permutations (List.range arguments.length)).filterMap
          fun permutation =>
            match applyArgPermute real wire permutation with
            | .error _ => none
            | .ok applied => some (.argPermute wire permutation applied)

private def argContractCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun wire =>
    match (real.val.wires wire).sig with
    | .iota => []
    | .rel arguments =>
        (List.range arguments.length).filterMap fun position =>
          match applyArgContract real wire position with
          | .error _ => none
          | .ok applied => some (.argContract wire position applied)

private def argDuplicateCandidates
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    List (CompiledPrimitiveStep orientation real) :=
  real.val.wiresList.flatMap fun wire =>
    match (real.val.wires wire).sig with
    | .iota => []
    | .rel arguments =>
        (List.range arguments.length).filterMap fun position =>
          match applyArgDuplicate real wire position with
          | .error _ => none
          | .ok applied => some (.argDuplicate wire position applied)

private def inverseCandidates
    {planned : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep joinOrientation planned)
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    Except CompilerError
      (List (CompiledPrimitiveStep orientation real)) :=
  match step with
  | .wireSever .. => pure (wireJoinCandidates real orientation)
  | .wireJoin .. => pure (wireSeverCandidates real orientation)
  | .cutWrap .. => pure (cutAbsorbCandidates real orientation)
  | .cutAbsorb .. => pure (cutWrapCandidates real orientation)
  | .parallelSplit .. => pure (parallelFuseCandidates real orientation)
  | .parallelFuse .. => pure (parallelSplitCandidates real orientation)
  | .endsDelete wire _ =>
      pure
        (endsSpawnCandidates real
          (planned.val.wires wire).endpoints.length orientation)
  | .endsSpawn .. =>
      pure <|
        real.val.wiresList.filterMap fun wire =>
          match applyEndsDelete real wire orientation with
          | .error _ => none
          | .ok applied => some (.endsDelete wire applied)
  | .vacuousElim input _ =>
      pure (vacuousIntroCandidates real input.sig orientation)
  | .vacuousIntro .. => throw .malformedResidual
  | .arityShift .. => pure (arityUnshiftCandidates real orientation)
  | .arityUnshift .. => throw .malformedResidual
  | .argPermute .. => pure (argPermuteCandidates real orientation)
  | .argDuplicate .. => pure (argContractCandidates real orientation)
  | .argContract .. => pure (argDuplicateCandidates real orientation)
  | .argDrop wire position _ =>
      match (planned.val.wires wire).sig with
      | .iota => throw .malformedResidual
      | .rel arguments =>
          match arguments[position]? with
          | none => throw .malformedResidual
          | some signature =>
              pure
                (argExtendCandidates real position signature orientation)
  | .argExtend _ position _ _ _ =>
      pure (argDropCandidates real position orientation)
  | .applyFormal .. =>
      pure (abstractFormalCandidates real orientation)
  | .abstractFormal .. => throw .malformedResidual
  | .identityLeaf .. =>
      pure (identityAbstractCandidates real orientation)
  | .identityAbstract .. => throw .malformedResidual
  | .refLeaf .. =>
      pure (refAbstractCandidates real orientation)
  | .refAbstract .. => throw .malformedResidual

private def invertStep
    {planned : CheckedDiagram definitions}
    (step : CompiledPrimitiveStep joinOrientation planned)
    (real : CheckedDiagram definitions)
    (orientation : Orientation) :
    Except CompilerError (InverseStepRun orientation real planned) := do
  let candidates ← inverseCandidates step real orientation
  requireOption .redundancyMismatch <|
    selectInverse? planned candidates

private structure ReversedProgram
    (orientation : Orientation)
    (real planned : CheckedDiagram definitions) where
  program : PrimitiveProgram orientation real
  normalizedIso : ConcreteIso program.target.val planned.val

private def reversePrimitiveProgram :
    {planned : CheckedDiagram definitions} →
    (program : PrimitiveProgram joinOrientation planned) →
    (real : CheckedDiagram definitions) →
    ConcreteIso program.target.val real.val →
    (orientation : Orientation) →
    Except CompilerError (ReversedProgram orientation real planned)
  | planned, .nil _, real, finalIso, _ =>
      .ok
        { program := .nil real
          normalizedIso := finalIso.symm }
  | planned, .cons head tail, real, finalIso, orientation => do
      let reversedTail ←
        reversePrimitiveProgram tail real finalIso orientation
      let inverse ←
        invertStep head reversedTail.program.target orientation
      pure
        { program :=
            reversedTail.program.append
              (.cons inverse.step (.nil inverse.step.target))
          normalizedIso := by
            simpa only [PrimitiveProgram.target_append] using
              inverse.normalizedIso }

/-- A successful join compilation and its independently checked redundancy. -/
structure CompiledRelationJoin
    {source : CheckedDiagram definitions}
    (input : MonolithicRelationJoinInput source) where
  monolithic : AppliedMonolithicRelationJoin source input
  arguments : List Sig
  sourceSignature : (source.val.wires input.wire).sig = .rel arguments
  boundary : JoinBoundaryReceipt input arguments
  program : PrimitiveProgram input.orientation source
  remainingTracked : List program.target.val.WireId
  trackedEmpty : remainingTracked = []
  normalizedIso :
    ConcreteIso program.target.val monolithic.target.val

/-- A successful sever compilation and its independently checked redundancy. -/
structure CompiledRelationSever
    {source : CheckedDiagram definitions}
    (input : MonolithicRelationSeverInput source) where
  monolithic : AppliedMonolithicRelationSever source input
  program : PrimitiveProgram input.orientation source
  normalizedIso :
    ConcreteIso program.target.val monolithic.target.val

namespace CompiledRelationJoin

/--
Transport any ordered final boundary through the checked normalization
isomorphism.  `List.map` intentionally preserves positions and repeated
aliases; this is the compiler's exact boundary transport, not a set image.
-/
def transportBoundary
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (compiled : CompiledRelationJoin input)
    (boundary : List compiled.program.target.val.WireId) :
    List compiled.monolithic.target.val.WireId :=
  boundary.map compiled.normalizedIso.wires

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
      compiled.normalizedIso.wires (boundary.get position) := by
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
  boundary.map compiled.normalizedIso.wires

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
      compiled.normalizedIso.wires (boundary.get position) := by
  simp [transportBoundary]

end CompiledRelationSever

private def compileAppliedRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source)
    (monolithic : AppliedMonolithicRelationJoin source input) :
    Except CompilerError (CompiledRelationJoin input) := do
  let arguments := monolithic.arguments
  let sourceSignature := monolithic.sourceSignature
  let boundary : JoinBoundaryReceipt input arguments :=
    { marker := ()
      boundaryLength := monolithic.boundaryLength
      formalSignatures := monolithic.formalSignatures
      parameterSignatures := monolithic.parameterSignatures }
  let ambientStubs := input.content.val.boundary.drop arguments.length
  let ambients := ambientStubs.zip input.parameters
  let residual :=
    initialContentResidual input.content monolithic.contentCompilation
      arguments.length
  let compiled ←
    compileResidual source input.wire input.content residual ambients []
      input.orientation
  have trackedEmpty : compiled.tracked = [] :=
    List.eq_nil_of_length_eq_zero compiled.trackedLength
  let normalizedIso ←
    requireOption .redundancyMismatch <|
      ConcreteIsoSearch.findConcreteIso?
        compiled.program.target.val monolithic.target.val
  pure
    { monolithic := monolithic
      arguments := arguments
      sourceSignature := sourceSignature
      boundary := boundary
      program := compiled.program
      remainingTracked := compiled.tracked
      trackedEmpty := trackedEmpty
      normalizedIso := normalizedIso }

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
    (applyMonolithicRelationJoin source input).mapError
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
  let inverseInput := monolithic.inverseJoinInput
  let planned ←
    compileAppliedRelationJoin monolithic.target inverseInput
      monolithic.inverseJoinApplied
  let reconstruction ←
    requireOption .redundancyMismatch <|
      ConcreteIsoSearch.findConcreteIso?
        planned.program.target.val source.val
  let reversed ←
    reversePrimitiveProgram planned.program source reconstruction
      input.orientation
  pure
    { monolithic := monolithic
      program := reversed.program
      normalizedIso := reversed.normalizedIso }

end WirePrimitive

end VisualProof
