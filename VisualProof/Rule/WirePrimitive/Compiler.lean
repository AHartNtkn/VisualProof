import VisualProof.Rule.WirePrimitive.CompilerTermination
import VisualProof.Rule.WirePrimitive.ArgumentsDropTransport
import VisualProof.Rule.WirePrimitive.ArgumentsExtendTransport
import VisualProof.Rule.WirePrimitive.ArgumentsArityTransport
import VisualProof.Rule.WirePrimitive.ArgumentsDuplicateTransport
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
def initialIntrinsicResidual
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

private def IntrinsicCompilerResidual.execution
    (residual : IntrinsicCompilerResidual source context) :
    IntrinsicExecutionResidual source context where
  body := residual.body
  wire := residual.wire
  formals := residual.formals
  ambients := residual.ambients.map fun binding =>
    (binding.value, binding.wire)

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
  intrinsicRegionSize residual.body
decreasing_by
  all_goals
    try simp_all [bodyExact, intrinsicRegionSize, intrinsicItemSeqSize,
      intrinsicItemSize]
  all_goals
    have headPositive := intrinsicItemSize_positive head
    have nextPositive := intrinsicItemSize_positive next
    omega

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
  normalizedIso : ConcreteIso step.target.val planned.val

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
          normalizedIso := inverse.targetIso }
  | .wireJoin _ _ applied => do
      let inverse ←
        (Partition.invertWireJoinTransported applied real targetIso
          orientation).mapError .partitionRejected
      pure
        { step := .wireSever inverse.input inverse.orientationExact
            inverse.applied
          normalizedIso := inverse.targetIso }
  | .arityShift _ _ applied => do
      let inverseWire := targetIso.wires.symm applied.targetWire
      let wireExact := targetIso.wires.right_inv applied.targetWire
      let inversePosition := applied.sourceArgumentList.length
      let inverseApplied ←
        (applyArityUnshift real inverseWire inversePosition).mapError
          .argumentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .arityUnshift inverseWire inversePosition inverseApplied
      let normalizedIso := applied.inverseTransportIso inverseApplied
        targetIso wireExact
      pure { step := inverseStep, normalizedIso := normalizedIso }
  | .argPermute _ _ applied => do
      let inverseWire := targetIso.wires.symm applied.targetWire
      let inverse := applied.inversePermutation
      let inverseApplied ←
        (applyArgPermute real inverseWire inverse).mapError
          .argumentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .argPermute inverseWire inverse inverseApplied
      let normalizedIso := applied.inverseTransportIso inverseApplied
        targetIso (targetIso.wires.right_inv applied.targetWire)
      pure { step := inverseStep, normalizedIso := normalizedIso }
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
          let normalizedIso := applied.inverseTransportIso targetIso wireExact
            inverseApplied argumentExact
          pure { step := inverseStep, normalizedIso := normalizedIso }
  | .argExtend _ position _ _ applied => do
      let inverseWire := targetIso.wires.symm applied.targetWire
      let wireExact := targetIso.wires.right_inv applied.targetWire
      let inverseApplied ←
        (applyArgDrop real inverseWire position orientation).mapError
          .argumentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .argDrop inverseWire position inverseApplied
      let normalizedIso := applied.inverseTransportIso inverseApplied targetIso
        wireExact
      pure { step := inverseStep, normalizedIso := normalizedIso }
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
      let normalizedIso := landing.iso
      pure { step := inverseStep, normalizedIso := normalizedIso }
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
      let normalizedIso := landing.iso
      pure { step := inverseStep, normalizedIso := normalizedIso }
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
      let normalizedIso := landing.iso
      pure { step := inverseStep, normalizedIso := normalizedIso }
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
      let normalizedIso := landing.iso
      pure { step := inverseStep, normalizedIso := normalizedIso }
  | .cutWrap _ applied => do
      let inverseWire := applied.transportedInverseWire targetIso
      let inverseApplied ←
        (applyCutAbsorb real inverseWire).mapError .contentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .cutAbsorb inverseWire inverseApplied
      let landing ←
        (applied.inverseTransport targetIso inverseApplied).mapError
          .contentRejected
      let normalizedIso := landing.iso
      pure { step := inverseStep, normalizedIso := normalizedIso }
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
      let normalizedIso := landing.iso
      pure { step := inverseStep, normalizedIso := normalizedIso }
  | .argDuplicate _ position applied => do
      let inverseWire := targetIso.wires.symm applied.targetWire
      let wireExact := targetIso.wires.right_inv applied.targetWire
      let inverseApplied ←
        (applyArgContract real inverseWire position).mapError
          .argumentRejected
      let inverseStep : CompiledPrimitiveStep orientation real :=
        .argContract inverseWire position inverseApplied
      let normalizedIso := applied.inverseTransportIso inverseApplied targetIso
        wireExact
      pure { step := inverseStep, normalizedIso := normalizedIso }
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
      let normalizedIso := Vacuity.identityIso planned.val planned.property
      pure { step := inverseStep, normalizedIso := normalizedIso }
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
          normalizedIso := finalIso.symm }
  | planned, .cons head tail, real, finalIso, orientation => do
      let reversedTail ←
        reversePrimitiveProgram tail real finalIso orientation
      let inverse ←
        invertStep head reversedTail.program.target
          reversedTail.normalizedIso orientation
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
  let residual := initialIntrinsicResidual monolithic
  let compiled ←
    compileResidual residual [] input.orientation
  have trackedEmpty : compiled.tracked = [] :=
    List.eq_nil_of_length_eq_zero compiled.trackedLength
  let constructionLanding ←
    requireOption .redundancyMismatch <|
      ConcreteIsoSearch.findConcreteIso?
        compiled.construction.1.val monolithic.target.val
  let normalizedIso := compiled.construction.2.trans constructionLanding
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
