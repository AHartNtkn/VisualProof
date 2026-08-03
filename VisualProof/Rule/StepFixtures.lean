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

/-! Replacement carrier fixtures use an occurrence with both a repeated
boundary survivor and genuinely internal removed wires. -/

private structure MainPatternCompilationReceipt where
  compilation : OpenCompilation OccurrenceFixtures.mainPattern
  accepted : compileOpen OccurrenceFixtures.mainPattern = some compilation

private def mainPatternCompilationReceipt :
    MainPatternCompilationReceipt := by
  match accepted : compileOpen OccurrenceFixtures.mainPattern with
  | none =>
      have present :
          (compileOpen OccurrenceFixtures.mainPattern).isSome = true := by
        native_decide
      rw [accepted] at present
      contradiction
  | some compilation => exact ⟨compilation, accepted⟩

private def replacementRuleTheorem : RuleTheorem.{0} Definitions.nil where
  arguments := checkedBoundarySigs OccurrenceFixtures.mainPattern
  left := OccurrenceFixtures.mainPattern
  right := OccurrenceFixtures.mainPattern
  leftBoundary := rfl
  rightBoundary := rfl
  leftCompilation := mainPatternCompilationReceipt.compilation
  leftCompilationAccepted := mainPatternCompilationReceipt.accepted
  rightCompilation := mainPatternCompilationReceipt.compilation
  rightCompilationAccepted := mainPatternCompilationReceipt.accepted
  valid := by
    intro _model _definitionEnv _lawful _values sourceDenotes
    exact sourceDenotes

private def replacementTheoremInput :
    TheoremApplication (definitions := Definitions.nil)
      OccurrenceFixtures.mainHost :=
  .forward replacementRuleTheorem .forward OccurrenceFixtures.mainOccurrence

private def replacementTheoremApplied :
    AppliedTheorem Definitions.nil OccurrenceFixtures.mainHost
      replacementTheoremInput :=
  (applyTheorem Definitions.nil OccurrenceFixtures.mainHost
    replacementTheoremInput).toOption.get (by native_decide)

private theorem theoremBoundaryRetained :
    replacementTheoremApplied.rawWireRetained
      OccurrenceFixtures.mainBoundaryWire := by
  native_decide

private theorem theoremInternalRemoved :
    ¬ replacementTheoremApplied.rawWireRetained
      OccurrenceFixtures.mainChildWire := by
  native_decide

/-- Accepted theorem replacement maps its repeated boundary survivor. -/
example :
    replacementTheoremApplied.rawWireImage?
        OccurrenceFixtures.mainBoundaryWire =
      some (replacementTheoremApplied.rawRetainedWire
        OccurrenceFixtures.mainBoundaryWire theoremBoundaryRetained) :=
  replacementTheoremApplied.rawWireImage_of_mem
    OccurrenceFixtures.mainBoundaryWire theoremBoundaryRetained

/-- The same accepted theorem replacement rejects an internal removed wire. -/
example :
    replacementTheoremApplied.rawWireImage?
      OccurrenceFixtures.mainChildWire = none :=
  replacementTheoremApplied.rawWireImage_eq_none_of_not_mem
    OccurrenceFixtures.mainChildWire theoremInternalRemoved

/-- The accepted theorem carrier is injective on every successful image. -/
example {left right : OccurrenceFixtures.mainHost.val.WireId}
    {mapped : replacementTheoremApplied.target.val.WireId}
    (leftMapped : replacementTheoremApplied.rawWireImage? left = some mapped)
    (rightMapped : replacementTheoremApplied.rawWireImage? right = some mapped) :
    left = right :=
  replacementTheoremApplied.rawWireImage_injective leftMapped rightMapped

/-- The accepted theorem carrier preserves the retained boundary signature. -/
example :
    (replacementTheoremApplied.target.val.wires
      (replacementTheoremApplied.rawRetainedWire
        OccurrenceFixtures.mainBoundaryWire theoremBoundaryRetained)).sig =
      (OccurrenceFixtures.mainHost.val.wires
        OccurrenceFixtures.mainBoundaryWire).sig :=
  replacementTheoremApplied.rawWireImage_signature
    (replacementTheoremApplied.rawWireImage_of_mem
      OccurrenceFixtures.mainBoundaryWire theoremBoundaryRetained)

private def replacementDefinitions : CheckedDefinitions :=
  (CheckedDefinitions.nil.snoc
    OccurrenceFixtures.mainPattern).toOption.get (by native_decide)

private structure ReplacementBodyReceipt where
  body : ResolvedDefinitionBody replacementDefinitions.intrinsic
    (checkedBoundarySigs OccurrenceFixtures.mainPattern)
  accepted : replacementDefinitions.resolveBody
      (.here : DefVar replacementDefinitions.intrinsic.signatures
        (checkedBoundarySigs OccurrenceFixtures.mainPattern)) = .ok body

private def replacementBodyReceipt : ReplacementBodyReceipt := by
  match accepted : replacementDefinitions.resolveBody
      (.here : DefVar replacementDefinitions.intrinsic.signatures
        (checkedBoundarySigs OccurrenceFixtures.mainPattern)) with
  | .error _ =>
      have present :
          (replacementDefinitions.resolveBody
            (.here : DefVar replacementDefinitions.intrinsic.signatures
              (checkedBoundarySigs OccurrenceFixtures.mainPattern))).toOption.isSome =
            true := by
        native_decide
      rw [accepted] at present
      change false = true at present
      contradiction
  | .ok body => exact ⟨body, accepted⟩

private def replacementBody := replacementBodyReceipt.body

private def replacementReference :
    CheckedReferenceFragment replacementDefinitions.intrinsic.signatures
      ⟨0, by native_decide⟩ :=
  (checkReferenceFragment replacementDefinitions.intrinsic.signatures
    ⟨0, by native_decide⟩).toOption.get (by native_decide)

private def replacementFoldedSource :
    CheckedDiagram replacementDefinitions.intrinsic.signatures :=
  ⟨replacementReference.fragment.val.diagram,
    replacementReference.fragment.property.diagram⟩

private def replacementUnfoldInput :
    UnfoldInput replacementDefinitions replacementFoldedSource where
  node := ⟨0, by native_decide⟩

private def replacementUnfolded :
    AppliedUnfold replacementDefinitions replacementFoldedSource
      replacementUnfoldInput :=
  (applyUnfold replacementDefinitions replacementFoldedSource
    replacementUnfoldInput).toOption.get (by native_decide)

private def unfoldBoundaryWire : replacementFoldedSource.val.WireId :=
  ⟨0, by native_decide⟩

private theorem unfoldBoundaryRetained :
    replacementUnfolded.rawWireRetained unfoldBoundaryWire := by
  native_decide

/-- Accepted unfolding maps its retained reference boundary exactly. -/
example : replacementUnfolded.rawWireImage? unfoldBoundaryWire =
    some (replacementUnfolded.rawRetainedWire
      unfoldBoundaryWire unfoldBoundaryRetained) :=
  replacementUnfolded.rawWireImage_of_mem
    unfoldBoundaryWire unfoldBoundaryRetained

/-- Every source identity in this canonical folded reference is retained, so
there is no removed source wire to exercise in the unfold direction. -/
example : ∀ wire : replacementFoldedSource.val.WireId,
    replacementUnfolded.rawWireRetained wire := by
  native_decide

/-- The accepted unfold carrier is injective on every successful image. -/
example {left right : replacementFoldedSource.val.WireId}
    {mapped : replacementUnfolded.target.val.WireId}
    (leftMapped : replacementUnfolded.rawWireImage? left = some mapped)
    (rightMapped : replacementUnfolded.rawWireImage? right = some mapped) :
    left = right :=
  replacementUnfolded.rawWireImage_injective leftMapped rightMapped

/-- The accepted unfold carrier preserves its retained boundary signature. -/
example :
    (replacementUnfolded.target.val.wires
      (replacementUnfolded.rawRetainedWire
        unfoldBoundaryWire unfoldBoundaryRetained)).sig =
      (replacementFoldedSource.val.wires unfoldBoundaryWire).sig :=
  replacementUnfolded.rawWireImage_signature
    (replacementUnfolded.rawWireImage_of_mem
      unfoldBoundaryWire unfoldBoundaryRetained)

private def replacementBodySource :
    CheckedDiagram replacementDefinitions.intrinsic.signatures :=
  ⟨replacementBody.body.val.diagram, replacementBody.body.property.diagram⟩

private def replacementBodyOccurrenceInput :
    OccurrenceInput replacementBody.body replacementBodySource where
  region := replacementBodySource.val.root
  regionMap := fun region => region
  nodeMap := fun node => node
  wireMap := fun wire => wire

private def replacementBodyOccurrence :
    Occurrence replacementBody.body replacementBodySource :=
  (checkOccurrence replacementBodyOccurrenceInput).toOption.get
    (by native_decide)

private def replacementFoldInput :
    FoldInput replacementDefinitions replacementBodySource where
  definition := ⟨0, by native_decide⟩
  body := replacementBody
  bodyAccepted := replacementBodyReceipt.accepted
  occurrence := replacementBodyOccurrence

private def replacementFolded :
    AppliedFold replacementDefinitions replacementBodySource
      replacementFoldInput :=
  (applyFold replacementDefinitions replacementBodySource
    replacementFoldInput).toOption.get (by native_decide)

private def foldBoundaryWire : replacementBodySource.val.WireId :=
  ⟨0, by native_decide⟩

private def foldInternalWire : replacementBodySource.val.WireId :=
  ⟨2, by native_decide⟩

private theorem foldBoundaryRetained :
    replacementFolded.rawWireRetained foldBoundaryWire := by
  native_decide

private theorem foldInternalRemoved :
    ¬ replacementFolded.rawWireRetained foldInternalWire := by
  native_decide

/-- Accepted folding maps its retained body boundary exactly. -/
example : replacementFolded.rawWireImage? foldBoundaryWire =
    some (replacementFolded.rawRetainedWire
      foldBoundaryWire foldBoundaryRetained) :=
  replacementFolded.rawWireImage_of_mem
    foldBoundaryWire foldBoundaryRetained

/-- The same accepted fold rejects a genuinely internal body wire. -/
example : replacementFolded.rawWireImage? foldInternalWire = none :=
  replacementFolded.rawWireImage_eq_none_of_not_mem
    foldInternalWire foldInternalRemoved

/-- The accepted fold carrier is injective on every successful image. -/
example {left right : replacementBodySource.val.WireId}
    {mapped : replacementFolded.target.val.WireId}
    (leftMapped : replacementFolded.rawWireImage? left = some mapped)
    (rightMapped : replacementFolded.rawWireImage? right = some mapped) :
    left = right :=
  replacementFolded.rawWireImage_injective leftMapped rightMapped

/-- The accepted fold carrier preserves its retained boundary signature. -/
example :
    (replacementFolded.target.val.wires
      (replacementFolded.rawRetainedWire
        foldBoundaryWire foldBoundaryRetained)).sig =
      (replacementBodySource.val.wires foldBoundaryWire).sig :=
  replacementFolded.rawWireImage_signature
    (replacementFolded.rawWireImage_of_mem
      foldBoundaryWire foldBoundaryRetained)

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
      (definitions := definitions.intrinsic) source)
    (orientationExact : input.orientation = orientation)
    (applied : AppliedTheorem definitions.intrinsic source input) :
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
