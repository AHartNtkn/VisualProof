import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawOriginFacts

namespace VisualProof

namespace MonolithicWireQuantifier

open ConcreteWireQuantifier

section RawRegionTrace

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

/-- Region origins carried by one construction prefix.  Unlike the final raw
atlas, this family is indexed by the prefix's own ordered step list. -/
abbrev RelationJoinPrefixRegionOrigin
    (steps : List (RelationJoinStep source dying content)) :=
  source.val.RegionId ⊕
    Σ _occurrence : Fin steps.length,
      { region : content.val.diagram.RegionId //
        region ≠ content.val.diagram.root }

namespace ConcreteWireQuantifier.RelationJoinSemanticTrace

private def priorRegionCast
    {current : CheckedDiagram definitions}
    (step : RelationJoinStep source dying content)
    (priorExact : step.prior = current) :
    current.val.RegionId → step.prior.val.RegionId :=
  cast (congrArg (fun diagram : CheckedDiagram definitions =>
    diagram.val.RegionId) priorExact.symm)

/-- Lift a prefix origin across a snoc. -/
def prefixRegionOriginLift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps →
    RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])
  | .inl region => .inl region
  | .inr ⟨occurrence, region⟩ =>
      .inr ⟨Fin.cast (by simp) (Fin.castAdd 1 occurrence), region⟩

/-- Construction-owned region landing relation for a proof-only join prefix.
The semantic trace is itself a proposition, so this relation records its
total landing without selecting a runtime carrier from proof data. -/
inductive PrefixRegionLands {args : List Sig} :
    ∀ {steps : List (RelationJoinStep source dying content)}
      {final : CheckedDiagram definitions}
      {finalRegionImage : source.val.RegionId → final.val.RegionId}
      {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
      {finalWireImage : source.val.WireId → final.val.WireId}
      {finalDying : final.val.WireId} {finalScope : final.val.RegionId},
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope →
      RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps → final.val.RegionId → Prop
  | nil (region : source.val.RegionId) :
      PrefixRegionLands RelationJoinSemanticTrace.nil (.inl region) region
  | snoc_prior
      {steps : List (RelationJoinStep source dying content)}
      {current : CheckedDiagram definitions}
      {currentRegionImage : source.val.RegionId → current.val.RegionId}
      {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
      {currentWireImage : source.val.WireId → current.val.WireId}
      {currentDying : current.val.WireId} {currentScope : current.val.RegionId}
      (trace : RelationJoinSemanticTrace source dying content parameters args
        steps current currentRegionImage currentNodeImage currentWireImage
          currentDying currentScope)
      (step : RelationJoinStep source dying content)
      (priorExact : step.prior = current)
      (priorRegionImageExact : HEq step.priorRegionImage currentRegionImage)
      (priorNodeImageExact : HEq step.priorNodeImage currentNodeImage)
      (priorWireImageExact : HEq step.priorWireImage currentWireImage)
      (priorDyingExact : HEq (step.priorWireImage dying) currentDying)
      (priorScopeExact : HEq
        (step.priorRegionImage (source.val.wires dying).scope) currentScope)
      (relationArgsExact : step.relationArgs = args)
      (sourceParametersExact : step.sourceParameters = parameters)
      {origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps}
      {target : current.val.RegionId}
      (landing : PrefixRegionLands trace origin target) :
      PrefixRegionLands
        (RelationJoinSemanticTrace.snoc trace step priorExact
          priorRegionImageExact priorNodeImageExact priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact sourceParametersExact)
        (prefixRegionOriginLift step origin)
        (step.checkedPriorRegion (priorRegionCast step priorExact target))
  | snoc_fresh
      {steps : List (RelationJoinStep source dying content)}
      {current : CheckedDiagram definitions}
      {currentRegionImage : source.val.RegionId → current.val.RegionId}
      {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
      {currentWireImage : source.val.WireId → current.val.WireId}
      {currentDying : current.val.WireId} {currentScope : current.val.RegionId}
      (trace : RelationJoinSemanticTrace source dying content parameters args
        steps current currentRegionImage currentNodeImage currentWireImage
          currentDying currentScope)
      (step : RelationJoinStep source dying content)
      (priorExact : step.prior = current)
      (priorRegionImageExact : HEq step.priorRegionImage currentRegionImage)
      (priorNodeImageExact : HEq step.priorNodeImage currentNodeImage)
      (priorWireImageExact : HEq step.priorWireImage currentWireImage)
      (priorDyingExact : HEq (step.priorWireImage dying) currentDying)
      (priorScopeExact : HEq
        (step.priorRegionImage (source.val.wires dying).scope) currentScope)
      (relationArgsExact : step.relationArgs = args)
      (sourceParametersExact : step.sourceParameters = parameters)
      (region : { region : content.val.diagram.RegionId //
        region ≠ content.val.diagram.root }) :
      PrefixRegionLands
        (RelationJoinSemanticTrace.snoc trace step priorExact
          priorRegionImageExact priorNodeImageExact priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact sourceParametersExact)
        (.inr ⟨Fin.cast (by simp) (Fin.last steps.length), region⟩)
        (step.checkedFragmentRegion region.1)

/-- The source origin's landing is the semantic trace's source-region image. -/
theorem prefixRegionLands_source
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinSemanticTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (region : source.val.RegionId) :
    PrefixRegionLands trace (.inl region) (finalRegionImage region) := by
  induction trace with
  | nil => exact PrefixRegionLands.nil region
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst_vars
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      simpa only [priorRegionCast, step.checkedRegionImage_eq_checkedPriorRegion]
        using
          (PrefixRegionLands.snoc_prior trace step rfl (by rfl) (by rfl)
            (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) induction)

/-- The final occurrence of a trace lands through exactly that step's fresh
fragment-region transport. -/
theorem prefixRegionLands_last
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    {currentRegionImage : source.val.RegionId → current.val.RegionId}
    {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
    {currentWireImage : source.val.WireId → current.val.WireId}
    {currentDying : current.val.WireId}
    {currentScope : current.val.RegionId}
    (trace : RelationJoinSemanticTrace source dying content parameters args
      steps current currentRegionImage currentNodeImage currentWireImage
        currentDying currentScope)
    (step : RelationJoinStep source dying content)
    (priorExact : step.prior = current)
    (priorRegionImageExact : HEq step.priorRegionImage currentRegionImage)
    (priorNodeImageExact : HEq step.priorNodeImage currentNodeImage)
    (priorWireImageExact : HEq step.priorWireImage currentWireImage)
    (priorDyingExact : HEq (step.priorWireImage dying) currentDying)
    (priorScopeExact : HEq
      (step.priorRegionImage (source.val.wires dying).scope) currentScope)
    (relationArgsExact : step.relationArgs = args)
    (sourceParametersExact : step.sourceParameters = parameters)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    PrefixRegionLands
      (RelationJoinSemanticTrace.snoc trace step priorExact priorRegionImageExact
        priorNodeImageExact priorWireImageExact priorDyingExact priorScopeExact
        relationArgsExact sourceParametersExact)
      (.inr ⟨Fin.cast (by simp) (Fin.last steps.length), region⟩)
      (step.checkedFragmentRegion region.1) := by
  exact PrefixRegionLands.snoc_fresh trace step priorExact
    priorRegionImageExact priorNodeImageExact priorWireImageExact
    priorDyingExact priorScopeExact relationArgsExact sourceParametersExact region

/-- Every neutral origin of a construction prefix has a region landing. -/
theorem prefixRegionLands_total
    {args : List Sig}
    {allSteps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinSemanticTrace source dying content parameters args
      allSteps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) allSteps) :
    ∃ target, PrefixRegionLands trace origin target := by
  induction trace with
  | nil =>
      cases origin with
      | inl region => exact ⟨region, PrefixRegionLands.nil region⟩
      | inr occurrence => exact Fin.elim0 occurrence.1
  | @snoc priorSteps current currentRegionImage currentNodeImage currentWireImage
      currentDying currentScope trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst_vars
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases origin with
      | inl region =>
          obtain ⟨prior, landing⟩ := induction (.inl region)
          refine ⟨step.checkedPriorRegion prior, ?_⟩
          simpa [prefixRegionOriginLift, priorRegionCast] using
            (PrefixRegionLands.snoc_prior trace step rfl (by rfl) (by rfl)
              (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) landing)
      | inr occurrence =>
          rcases occurrence with ⟨occurrence, region⟩
          let occurrence' : Fin (priorSteps.length + 1) :=
            Fin.cast (by simp) occurrence
          refine Fin.lastCases
            (motive := fun index => ∃ target, PrefixRegionLands _
              (.inr ⟨Fin.cast (by simp) index, region⟩) target)
            ?_ ?_ occurrence'
          · refine ⟨step.checkedFragmentRegion region.1, ?_⟩
            simpa using
              (PrefixRegionLands.snoc_fresh trace step rfl (by rfl) (by rfl)
                (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) region)
          · intro priorOccurrence
            obtain ⟨prior, landing⟩ := induction (.inr ⟨priorOccurrence, region⟩)
            refine ⟨step.checkedPriorRegion prior, ?_⟩
            simpa [prefixRegionOriginLift, priorRegionCast] using
              (PrefixRegionLands.snoc_prior trace step rfl (by rfl) (by rfl)
                (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) landing)

end ConcreteWireQuantifier.RelationJoinSemanticTrace

namespace ConcreteWireQuantifier.RelationJoinSemanticTrace

/-- Terminal raw-region landing: the prefix construction landing followed by
the exhausted-relation deletion's all-region transport. -/
def plainPrefixRegionLands
    (result : RelationJoinResult source dying content parameters)
  (origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) result.steps)
    (target : result.plainFinal.val.RegionId) : Prop :=
  ∃ bound, PrefixRegionLands result.semantic_trace
      origin bound ∧ target = result.plainBoundRegionImage bound

/-- Every raw neutral region origin survives terminal exhausted-wire deletion. -/
theorem plainPrefixRegionLands_total
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) result.steps) :
    ∃ target, plainPrefixRegionLands result origin target := by
  obtain ⟨bound, landing⟩ :=
    prefixRegionLands_total result.semantic_trace origin
  exact ⟨result.plainBoundRegionImage bound, bound, landing, rfl⟩

/-- The source portion of the raw terminal landing is the existing exact
source-region transport. -/
theorem plainPrefixRegionLands_source
    (result : RelationJoinResult source dying content parameters)
    (region : source.val.RegionId) :
    plainPrefixRegionLands result (.inl region)
      (result.plainBoundRegionImage (result.boundRegionImage region)) := by
  refine ⟨result.boundRegionImage region, ?_, rfl⟩
  exact prefixRegionLands_source result.semantic_trace region

end ConcreteWireQuantifier.RelationJoinSemanticTrace

end RawRegionTrace

end MonolithicWireQuantifier

end VisualProof
