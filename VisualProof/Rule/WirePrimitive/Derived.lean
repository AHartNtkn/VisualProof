import VisualProof.Rule.WirePrimitive.CompilerSoundness

namespace VisualProof
namespace WirePrimitive

open StructuralCore

/-- Refusal outcomes of the executable primitive-derivation layer. -/
inductive DerivedError
  | generatedDiagramRejected (error : WFError)
  | vacuousRejected (error : VacuousError)
  | structuralRejected (error : StructuralError)
  | compilerRejected (error : CompilerError)
  | constructionMismatch
  deriving Repr, DecidableEq

/-- Accepted raw arbitrary-content insertion, used only as a redundancy spec. -/
structure AcceptedRawInsertion
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    (input : StructuralInsertionInput base fragment) where
  private mk ::
  private attachment : ConcreteSpliceAttachment base input.site fragment
  private result : ConcreteSpliceResult attachment
  private accepted : splice attachment = .ok result

namespace AcceptedRawInsertion

/-- The exact checked pre-normalization splice specified by the receipt. -/
def target
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : AcceptedRawInsertion input) : CheckedDiagram definitions :=
  checked.result.raw

end AcceptedRawInsertion

/-- Check the arbitrary raw splice and the insertion polarity, without a tag. -/
def checkRawInsertion
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    (input : StructuralInsertionInput base fragment) :
    Except StructuralError (AcceptedRawInsertion input) := by
  match compileSite? base input.site with
  | none => exact .error .siteCompilationFailed
  | some siteCompiled =>
      let legal : Bool :=
        match input.orientation with
        | .forward => siteCompiled.frame.context.cutDepth % 2 == 1
        | .backward => siteCompiled.frame.context.cutDepth % 2 == 0
      if legal then
        match checkConcreteSpliceAttachment base input.site fragment input.target with
        | none => exact .error .attachmentRejected
        | some attachment =>
            match accepted : splice attachment with
            | .error error => exact .error (.spliceRejected error)
            | .ok result =>
                exact .ok (AcceptedRawInsertion.mk attachment result accepted)
      else
        cases orientation : input.orientation with
        | forward => exact .error .forwardInsertionRequiresNegative
        | backward => exact .error .backwardInsertionRequiresPositive

/-- Canonical nullary relation application used to ground arbitrary content. -/
private def nullaryAtomRaw
    (definitionCount : Nat) : OpenConcreteDiagram definitionCount where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 1
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .atom 0 []
      wires := fun _ =>
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .head⟩] } }
  boundary := [0]

private def checkNullaryAtom
    (definitions : List (List Sig)) :
    Except WFError (CheckedOpenDiagram definitions) := by
  let raw := nullaryAtomRaw definitions.length
  match accepted : ConcreteDiagram.checkWellFormed definitions raw.diagram with
  | .error error => exact .error error
  | .ok checked =>
      have generated : checked.val = raw.diagram :=
        ConcreteDiagram.checkWellFormed_preserves_input accepted
      exact .ok
        ⟨raw,
          { diagram := generated ▸ checked.property
            boundary_root_scoped := by
              simp [raw, nullaryAtomRaw] }⟩

/-- Canonical concrete introduction of one fresh endpoint-free wire. -/
private def vacuousBoundRaw
    (source : CheckedDiagram definitions)
    (site : source.val.RegionId)
    (signature : Sig) : ConcreteDiagram definitions.length where
  regionCount := source.val.regionCount
  nodeCount := source.val.nodeCount
  wireCount := source.val.wireCount + 1
  root := source.val.root
  regions := source.val.regions
  nodes := source.val.nodes
  wires := Fin.cases
    { sig := signature, scope := site, endpoints := [] }
    source.val.wires

private def shiftedWire
    (source : CheckedDiagram definitions)
    (site : source.val.RegionId)
    (signature : Sig)
    (wire : source.val.WireId) :
    (vacuousBoundRaw source site signature).WireId :=
  Fin.succ wire

private structure GeneratedChecked
    (definitions : List (List Sig))
    (raw : ConcreteDiagram definitions.length) where
  checked : CheckedDiagram definitions
  generated : checked.val = raw

private def checkGenerated
    (definitions : List (List Sig))
    (raw : ConcreteDiagram definitions.length) :
    Except WFError (GeneratedChecked definitions raw) := by
  match accepted : ConcreteDiagram.checkWellFormed definitions raw with
  | .error error => exact .error error
  | .ok checked =>
      exact .ok
        { checked := checked
          generated := ConcreteDiagram.checkWellFormed_preserves_input accepted }

private def requireOption (error : DerivedError) : Option α → Except DerivedError α
  | none => .error error
  | some value => .ok value

/-- Validate the construction-prescribed dense carrier correspondence. -/
private def denseIndexIso?
    {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length) :
    Option (ConcreteIso left right) := do
  if regionsExact : left.regionCount = right.regionCount then
    if nodesExact : left.nodeCount = right.nodeCount then
      if wiresExact : left.wireCount = right.wireCount then
        ConcreteIso.checkEquivs? left right
          (Data.Finite.FiniteEquiv.finCast regionsExact)
          (Data.Finite.FiniteEquiv.finCast nodesExact)
          (Data.Finite.FiniteEquiv.finCast wiresExact)
      else none
    else none
  else none

/-- Checked primitive construction that reproduces one raw structural insertion. -/
structure InsertionPrimitiveLanding
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : AcceptedRawInsertion input) where
  program : PrimitiveProgram input.orientation base
  constructionIso : ConcreteIso program.target.val checked.target.val

/--
Construct arbitrary raw structural insertion as vacuous nullary relation
introduction, nullary application spawn, and constructive relation grounding.
-/
def insertion_primitive_program
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    (checked : AcceptedRawInsertion input) :
    Except DerivedError (InsertionPrimitiveLanding checked) := do
  let boundRaw := vacuousBoundRaw base input.site (.rel [])
  let generatedBound ←
    (checkGenerated definitions boundRaw).mapError .generatedDiagramRejected
  let bound := generatedBound.checked
  have regionCountExact : bound.val.regionCount = base.val.regionCount := by
    rw [generatedBound.generated]
    rfl
  have wireCountExact : bound.val.wireCount = base.val.wireCount + 1 := by
    rw [generatedBound.generated]
    rfl
  let boundSite : bound.val.RegionId :=
    Fin.cast regionCountExact.symm input.site
  let boundWire (wire : base.val.WireId) : bound.val.WireId :=
    Fin.cast wireCountExact.symm (Fin.succ wire)
  let vacuousInput : VacuousInput base bound :=
    { site := input.site, sig := .rel [] }
  let vacuousChecked ←
    (checkVacuous vacuousInput).mapError .vacuousRejected
  let fresh : bound.val.WireId := ⟨0, by rw [wireCountExact]; omega⟩
  let deletionIso ←
    requireOption .constructionMismatch <|
      denseIndexIso? base.val
        (ConcreteDiagram.DenseErasure.eraseWireCandidate bound fresh)
  if siteExact : deletionIso.regions input.site =
      ConcreteWireQuantifier.ExhaustedWireRemovalSemantics.targetRegion
        bound fresh (bound.val.wires fresh).scope then
    if signatureExact : (bound.val.wires fresh).sig = .rel [] then
      if endpointsExact : (bound.val.wires fresh).endpoints = [] then
        let deletion := Vacuity.recordElimination vacuousChecked fresh
          deletionIso siteExact signatureExact endpointsExact
        let vacuousStep : CompiledPrimitiveStep input.orientation base :=
          .vacuousIntro vacuousInput vacuousChecked deletion
        let atom ←
          (checkNullaryAtom definitions).mapError .generatedDiagramRejected
        let atomInput : StructuralInsertionInput vacuousStep.target atom :=
          { orientation := input.orientation
            site := boundSite
            target := fun _ => fresh }
        let atomChecked ←
          (checkStructuralInsertion atomInput).mapError .structuralRejected
        if atomTag : atomChecked.tag = .atomSpawn then
          let atomStep :
              CompiledPrimitiveStep input.orientation vacuousStep.target :=
            .atomSpawn atomInput rfl atomChecked atomTag
          let relationWire := atomChecked.rawHostWire fresh
          let parameters :=
            (Data.Finite.allFin fragment.val.boundary.length).map fun position =>
              atomChecked.rawHostWire
                (boundWire (input.target position))
          let joinInput : MonolithicRelationJoinInput atomStep.target :=
            { orientation := input.orientation
              wire := relationWire
              content := fragment
              parameters := parameters }
          let compiled ←
            (compileRelationJoin atomStep.target joinInput).mapError
              .compilerRejected
          let terminalIso ←
            requireOption .constructionMismatch <|
              denseIndexIso? compiled.monolithic.plainFinal.val
                checked.target.val
          let initialProgram : PrimitiveProgram input.orientation base :=
            PrimitiveProgram.cons vacuousStep
              (PrimitiveProgram.cons atomStep
                (PrimitiveProgram.nil atomStep.target))
          let program := initialProgram.append compiled.program
          pure
            { program := program
              constructionIso := by
                simpa [program] using
                  compiled.constructionIso.trans terminalIso }
        else
          throw .constructionMismatch
      else
        throw .constructionMismatch
    else
      throw .constructionMismatch
  else
    throw .constructionMismatch

/-- A constructed insertion program has exactly the raw structural landing. -/
theorem insertion_redundant
    {base : CheckedDiagram definitions}
    {fragment : CheckedOpenDiagram definitions}
    {input : StructuralInsertionInput base fragment}
    {checked : AcceptedRawInsertion input}
    (landing : InsertionPrimitiveLanding checked) :
    Nonempty (ConcreteIso landing.program.target.val checked.target.val) :=
  ⟨landing.constructionIso⟩

end WirePrimitive
end VisualProof
