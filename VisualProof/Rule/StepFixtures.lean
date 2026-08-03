import VisualProof.Rule.Soundness
import VisualProof.Diagram.Concrete.Subgraph.SpliceExamples

namespace VisualProof

open ConcreteSpliceExamples

private def firstDefinitions : CheckedDefinitions :=
  (CheckedDefinitions.nil.snoc oneStub).toOption.get (by native_decide)

private def firstBody :
    ResolvedDefinitionBody firstDefinitions.intrinsic [.iota] :=
  (firstDefinitions.resolveBody (.here :
      DefVar firstDefinitions.intrinsic.signatures [.iota])).toOption.get
    (by native_decide)

example : checkedBoundarySigs firstBody.body = [.iota] :=
  firstBody.boundarySignatures

private def firstReference :
    CheckedReferenceFragment firstDefinitions.intrinsic.signatures
      ⟨0, by native_decide⟩ :=
  (checkReferenceFragment firstDefinitions.intrinsic.signatures
      ⟨0, by native_decide⟩).toOption.get (by native_decide)

example :
    checkedBoundarySigs firstReference.fragment = [.iota] := by
  native_decide

private def foldedSource :
    CheckedDiagram firstDefinitions.intrinsic.signatures :=
  ⟨firstReference.fragment.val.diagram,
    firstReference.fragment.property.diagram⟩

private def unfoldInput : UnfoldInput firstDefinitions foldedSource where
  node := ⟨0, by native_decide⟩

private def unfolded : AppliedUnfold firstDefinitions foldedSource unfoldInput :=
  (applyUnfold firstDefinitions foldedSource unfoldInput).toOption.get
    (by native_decide)

example : unfolded.tag = .unfold := rfl

private def fixtureReceipt
    (source rawTarget : CheckedDiagram definitions) :
    StepReceipt source rawTarget where
  provenance := WireProvenance.none source.val
    (ConcreteDiagram.normalizeIdentities rawTarget).target.val
  rawTransport := WireTransport.none source.val rawTarget.val

variable {definitions : CheckedDefinitions} {orientation : Orientation}

/-! Every primitive constructor accepts only its owning checked compiler
receipt, and its public tag is pinned independently of receipt contents. -/

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .refSpawn) :
    (ProofStep.refSpawn primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .refSpawn := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .atomSpawn) :
    (ProofStep.atomSpawn primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .atomSpawn := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .identityInsert) :
    (ProofStep.identityInsert primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .identityInsert := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .wireJoin) :
    (ProofStep.wireJoin primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .wireJoin := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .erasure) :
    (ProofStep.erasure primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .erasure := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .wireSever) :
    (ProofStep.wireSever primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .wireSever := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .vacuousIntro) :
    (ProofStep.vacuousIntro primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .vacuousIntro := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .vacuousElim) :
    (ProofStep.vacuousElim primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .vacuousElim := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .cutWrap) :
    (ProofStep.cutWrap primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .cutWrap := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .cutAbsorb) :
    (ProofStep.cutAbsorb primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .cutAbsorb := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .parallelSplit) :
    (ProofStep.parallelSplit primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .parallelSplit := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .parallelFuse) :
    (ProofStep.parallelFuse primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .parallelFuse := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .endsDelete) :
    (ProofStep.endsDelete primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .endsDelete := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .endsSpawn) :
    (ProofStep.endsSpawn primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .endsSpawn := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .arityShift) :
    (ProofStep.arityShift primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .arityShift := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .arityUnshift) :
    (ProofStep.arityUnshift primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .arityUnshift := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .argPermute) :
    (ProofStep.argPermute primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .argPermute := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .argDuplicate) :
    (ProofStep.argDuplicate primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .argDuplicate := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .argContract) :
    (ProofStep.argContract primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .argContract := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .argDrop) :
    (ProofStep.argDrop primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .argDrop := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .argExtend) :
    (ProofStep.argExtend primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .argExtend := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .applyFormal) :
    (ProofStep.applyFormal primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .applyFormal := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .abstractFormal) :
    (ProofStep.abstractFormal primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .abstractFormal := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .identityLeaf) :
    (ProofStep.identityLeaf primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .identityLeaf := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .identityAbstract) :
    (ProofStep.identityAbstract primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .identityAbstract := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .refLeaf) :
    (ProofStep.refLeaf primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .refLeaf := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (primitive : WirePrimitive.CompiledPrimitiveStep orientation source)
    (tagExact : primitive.tag = .refAbstract) :
    (ProofStep.refAbstract primitive tagExact
      (fixtureReceipt source primitive.target)).tag = .refAbstract := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    {pattern : CheckedOpenDiagram definitions.intrinsic.signatures}
    {selection : CheckedSelection source} {occurrence : Occurrence pattern source}
    (input : StructuralCore.OrdinaryIterationInput selection occurrence)
    (checked : StructuralCore.CheckedOrdinaryIteration input) :
    (ProofStep.iteration (definitions := definitions)
      (orientation := orientation) input checked
      (fixtureReceipt source checked.target)).tag = .iteration := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    {pattern : CheckedOpenDiagram definitions.intrinsic.signatures}
    {innerSelection : CheckedSelection source}
    {inner : Occurrence pattern source}
    {justifierSelection : CheckedSelection source}
    {justifier : Occurrence pattern source}
    (input : StructuralCore.OrdinaryDeiterationInput innerSelection inner
      justifierSelection justifier)
    (checked : StructuralCore.CheckedOrdinaryDeiteration input) :
    (ProofStep.deiteration (definitions := definitions)
      (orientation := orientation) input checked
      (fixtureReceipt source checked.target)).tag = .deiteration := rfl

example {source doubled : CheckedDiagram definitions.intrinsic.signatures}
    (input : StructuralCore.DoubleCutInput source doubled)
    (checked : StructuralCore.CheckedDoubleCut input) :
    (ProofStep.doubleCutIntro (definitions := definitions)
      (orientation := orientation) input checked
      (fixtureReceipt source checked.doubled)).tag = .doubleCutIntro := rfl

example {source plain : CheckedDiagram definitions.intrinsic.signatures}
    (input : StructuralCore.DoubleCutInput plain source)
    (checked : StructuralCore.CheckedDoubleCut input) :
    (ProofStep.doubleCutElim (definitions := definitions)
      (orientation := orientation) input checked
      (fixtureReceipt source checked.plain)).tag = .doubleCutElim := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (input : TheoremApplication
      (definitions := definitions.intrinsic.signatures) source)
    (orientationExact : input.orientation = orientation)
    (applied : AppliedTheorem source input) :
    (ProofStep.theorem (definitions := definitions) input orientationExact
      applied (fixtureReceipt source applied.target)).tag = .theorem := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (input : UnfoldInput definitions source)
    (applied : AppliedUnfold definitions source input) :
    (ProofStep.unfold (orientation := orientation) input applied
      (fixtureReceipt source applied.target)).tag = .unfold := rfl

example {source : CheckedDiagram definitions.intrinsic.signatures}
    (input : FoldInput definitions source)
    (applied : AppliedFold definitions source input) :
    (ProofStep.fold (orientation := orientation) input applied
      (fixtureReceipt source applied.target)).tag = .fold := rfl

/-- This proof intentionally has one branch per constructor. Adding a
constructor without extending the durable tag vocabulary makes it fail to
compile; `StepTag.all_nodup` separately rejects duplicate durable tags. -/
theorem proofStep_tag_exhaustive
    {source : CheckedDiagram definitions.intrinsic.signatures}
    (step : ProofStep definitions orientation source) :
    step.tag ∈ StepTag.all := by
  cases step <;> simp [ProofStep.tag, StepTag.all]

example : StepTag.all.length = 34 := StepTag.all_length
example : StepTag.all.Nodup := StepTag.all_nodup

private def secondDefinitions : CheckedDefinitions :=
  (firstDefinitions.snoc firstBody.body).toOption.get (by native_decide)

private def olderBody :
    ResolvedDefinitionBody secondDefinitions.intrinsic [.iota] :=
  (secondDefinitions.resolveBody (.there .here :
      DefVar secondDefinitions.intrinsic.signatures [.iota])).toOption.get
    (by native_decide)

/-- An earlier concrete definition remains resolvable after a later snoc and
retains its exact ordered boundary signature. -/
example : checkedBoundarySigs olderBody.body = [.iota] :=
  olderBody.boundarySignatures

end VisualProof
