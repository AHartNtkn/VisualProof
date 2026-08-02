import VisualProof.Rule.MonolithicWireQuantifierRawRegionTraceData

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

/-- The new occurrence origin introduced by one visible snoc. -/
def prefixRegionFreshOrigin
    {spine : RelationJoinSnocSteps (source := source) (dying := dying)
      (content := content)}
    (step : RelationJoinStep source dying content)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (RelationJoinSnocSteps.snoc spine step).toList :=
  .inr ⟨Fin.cast (by
    simp only [RelationJoinSnocSteps.toList, List.length_append,
      List.length_singleton]) (Fin.last spine.toList.length), region⟩

theorem prefixRegionOriginLift_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (prefixRegionOriginLift
      (steps := steps) step) := by
  intro left right same
  cases left with
  | inl leftRegion =>
      cases right with
      | inl rightRegion =>
          exact congrArg Sum.inl (Sum.inl.inj same)
      | inr rightOccurrence => cases same
  | inr leftOccurrence =>
      cases right with
      | inl rightRegion => cases same
      | inr rightOccurrence =>
          rcases leftOccurrence with ⟨leftIndex, leftRegion⟩
          rcases rightOccurrence with ⟨rightIndex, rightRegion⟩
          have sigmaSame := Sum.inr.inj same
          have mappedIndexSame := congrArg Sigma.fst sigmaSame
          have indexSame : leftIndex = rightIndex := by
            apply Fin.ext
            simpa [prefixRegionOriginLift] using
              congrArg Fin.val mappedIndexSame
          have regionSame : leftRegion = rightRegion := by
            exact congrArg Sigma.snd sigmaSame
          cases indexSame
          cases regionSame
          rfl

theorem prefixRegionOriginLift_ne_fresh
    {spine : RelationJoinSnocSteps (source := source) (dying := dying)
      (content := content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) spine.toList)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    prefixRegionOriginLift step origin ≠
      prefixRegionFreshOrigin (spine := spine) step region := by
  intro same
  cases origin with
  | inl sourceRegion => cases same
  | inr occurrence =>
      rcases occurrence with ⟨index, priorRegion⟩
      have sigmaSame := Sum.inr.inj same
      have indexSame := congrArg Sigma.fst sigmaSame
      have values := congrArg Fin.val indexSame
      have bound := index.isLt
      simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_last] at values
      omega

theorem prefixRegionFreshOrigin_injective
    {spine : RelationJoinSnocSteps (source := source) (dying := dying)
      (content := content)}
    (step : RelationJoinStep source dying content)
    {left right : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }}
    (same : prefixRegionFreshOrigin (spine := spine) step left =
      prefixRegionFreshOrigin (spine := spine) step right) :
    left = right := by
  have sigmaSame := Sum.inr.inj same
  exact congrArg Sigma.snd sigmaSame

/-- Reindex an existing semantic trace by the canonical data-bearing spine for
its ordered step list. -/
def canonicalSpineAgreement
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinSemanticTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    RelationJoinSemanticTrace source dying content parameters args
      (RelationJoinSnocSteps.ofList steps).toList final finalRegionImage
        finalNodeImage finalWireImage finalDying finalScope := by
  simpa only [RelationJoinSnocSteps.toList_ofList] using trace

/-- Construction-owned region landing relation indexed by the visible snoc
spine.  The semantic proof certifies agreement with the spine, but does not own
or conceal its nil/snoc shape. -/
inductive PrefixRegionLands {args : List Sig} :
    ∀ (spine : RelationJoinSnocSteps (source := source) (dying := dying)
        (content := content))
      {final : CheckedDiagram definitions}
      {finalRegionImage : source.val.RegionId → final.val.RegionId}
      {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
      {finalWireImage : source.val.WireId → final.val.WireId}
      {finalDying : final.val.WireId} {finalScope : final.val.RegionId},
      RelationJoinSemanticTrace source dying content parameters args spine.toList
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope →
      RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
        (content := content) spine.toList → final.val.RegionId → Prop
  | nil (region : source.val.RegionId) :
      ∀ {origin target},
        origin = .inl region → target = region →
        PrefixRegionLands .nil RelationJoinSemanticTrace.nil origin target
  | snoc_prior
      {spine : RelationJoinSnocSteps (source := source) (dying := dying)
        (content := content)}
      {current : CheckedDiagram definitions}
      {currentRegionImage : source.val.RegionId → current.val.RegionId}
      {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
      {currentWireImage : source.val.WireId → current.val.WireId}
      {currentDying : current.val.WireId} {currentScope : current.val.RegionId}
      (trace : RelationJoinSemanticTrace source dying content parameters args
        spine.toList current currentRegionImage currentNodeImage currentWireImage
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
        (content := content) spine.toList}
      {target : current.val.RegionId}
      (landing : PrefixRegionLands spine trace origin target) :
      ∀ {nextOrigin nextTarget},
      nextOrigin = prefixRegionOriginLift step origin →
      nextTarget =
        step.checkedPriorRegion (priorRegionCast step priorExact target) →
      PrefixRegionLands
        (.snoc spine step)
        (RelationJoinSemanticTrace.snoc trace step priorExact
          priorRegionImageExact priorNodeImageExact priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact sourceParametersExact)
        nextOrigin nextTarget
  | snoc_fresh
      {spine : RelationJoinSnocSteps (source := source) (dying := dying)
        (content := content)}
      {current : CheckedDiagram definitions}
      {currentRegionImage : source.val.RegionId → current.val.RegionId}
      {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
      {currentWireImage : source.val.WireId → current.val.WireId}
      {currentDying : current.val.WireId} {currentScope : current.val.RegionId}
      (trace : RelationJoinSemanticTrace source dying content parameters args
        spine.toList current currentRegionImage currentNodeImage currentWireImage
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
      ∀ {origin target},
      origin = prefixRegionFreshOrigin (spine := spine) step region →
      target = step.checkedFragmentRegion region.1 →
      PrefixRegionLands
        (.snoc spine step)
        (RelationJoinSemanticTrace.snoc trace step priorExact
          priorRegionImageExact priorNodeImageExact priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact sourceParametersExact)
        origin target

/-- Exact origin transport induced by equality of data-bearing spines. -/
def prefixRegionOriginReindex
    {leftSpine rightSpine : RelationJoinSnocSteps (source := source)
      (dying := dying) (content := content)}
    (spineExact : leftSpine = rightSpine)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) leftSpine.toList) :
    RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) rightSpine.toList :=
  cast (congrArg (fun spine => RelationJoinPrefixRegionOrigin
    (source := source) (dying := dying) (content := content) spine.toList)
      spineExact) origin

@[simp] theorem prefixRegionOriginReindex_source
    {leftSpine rightSpine : RelationJoinSnocSteps (source := source)
      (dying := dying) (content := content)}
    (spineExact : leftSpine = rightSpine)
    (region : source.val.RegionId) :
    prefixRegionOriginReindex spineExact (.inl region) = .inl region := by
  cases spineExact
  rfl

/-- Transport a landing across equality of its data-bearing spines.  Agreement
proofs are propositions and hence irrelevant; the carrier origin is transported
only by the displayed spine equality. -/
private theorem PrefixRegionLands.reindex
    {args : List Sig}
    {leftSpine rightSpine : RelationJoinSnocSteps (source := source)
      (dying := dying) (content := content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (spineExact : leftSpine = rightSpine)
    {leftAgreement : RelationJoinSemanticTrace source dying content parameters
      args leftSpine.toList final finalRegionImage finalNodeImage finalWireImage
        finalDying finalScope}
    {rightAgreement : RelationJoinSemanticTrace source dying content parameters
      args rightSpine.toList final finalRegionImage finalNodeImage finalWireImage
        finalDying finalScope}
    {leftOrigin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) leftSpine.toList}
    {target : final.val.RegionId}
    (landing : PrefixRegionLands leftSpine leftAgreement leftOrigin target) :
    PrefixRegionLands rightSpine rightAgreement
      (prefixRegionOriginReindex spineExact leftOrigin) target := by
  subst rightSpine
  have agreementExact : leftAgreement = rightAgreement := Subsingleton.elim _ _
  cases agreementExact
  exact landing

/-- Totality transports contravariantly over exact spine equality, with no
choice of a landing carrier. -/
private theorem PrefixRegionLands.total_reindex
    {args : List Sig}
    {leftSpine rightSpine : RelationJoinSnocSteps (source := source)
      (dying := dying) (content := content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (spineExact : leftSpine = rightSpine)
    {leftAgreement : RelationJoinSemanticTrace source dying content parameters
      args leftSpine.toList final finalRegionImage finalNodeImage finalWireImage
        finalDying finalScope}
    {rightAgreement : RelationJoinSemanticTrace source dying content parameters
      args rightSpine.toList final finalRegionImage finalNodeImage finalWireImage
        finalDying finalScope}
    (leftTotal : ∀ origin, ∃ target,
      PrefixRegionLands leftSpine leftAgreement origin target)
    (rightOrigin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) rightSpine.toList) :
    ∃ target, PrefixRegionLands rightSpine rightAgreement rightOrigin target := by
  subst rightSpine
  have agreementExact : leftAgreement = rightAgreement := Subsingleton.elim _ _
  cases agreementExact
  exact leftTotal rightOrigin

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
    PrefixRegionLands (RelationJoinSnocSteps.ofList steps)
      (canonicalSpineAgreement trace) (.inl region)
      (finalRegionImage region) := by
  induction trace with
  | nil => exact PrefixRegionLands.nil region rfl rfl
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst_vars
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      have snocLanding : PrefixRegionLands
          (.snoc (RelationJoinSnocSteps.ofList _) step)
          (RelationJoinSemanticTrace.snoc (canonicalSpineAgreement trace) step
            rfl (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
              (by rfl))
          (.inl region) (step.checkedRegionImage region) :=
        PrefixRegionLands.snoc_prior (canonicalSpineAgreement trace) step
          rfl (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
            (by rfl) induction rfl (by
              rw [step.checkedRegionImage_eq_checkedPriorRegion]
              rfl)
      simpa only [prefixRegionOriginReindex_source] using
        PrefixRegionLands.reindex
          (RelationJoinSnocSteps.ofList_append_singleton _ step).symm
          snocLanding

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
    PrefixRegionLands (RelationJoinSnocSteps.ofList (steps ++ [step]))
      (canonicalSpineAgreement
        (RelationJoinSemanticTrace.snoc trace step priorExact
          priorRegionImageExact priorNodeImageExact priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact
          sourceParametersExact))
      (prefixRegionOriginReindex
        (RelationJoinSnocSteps.ofList_append_singleton steps step).symm
        (prefixRegionFreshOrigin
          (spine := RelationJoinSnocSteps.ofList steps) step region))
      (step.checkedFragmentRegion region.1) := by
  apply PrefixRegionLands.reindex
    (RelationJoinSnocSteps.ofList_append_singleton steps step).symm
  exact PrefixRegionLands.snoc_fresh
      (canonicalSpineAgreement trace) step priorExact priorRegionImageExact
      priorNodeImageExact priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact region rfl rfl

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
      (content := content)
      (RelationJoinSnocSteps.ofList allSteps).toList) :
    ∃ target, PrefixRegionLands (RelationJoinSnocSteps.ofList allSteps)
      (canonicalSpineAgreement trace) origin target := by
  induction trace with
  | nil =>
      cases origin with
      | inl region => exact ⟨region, PrefixRegionLands.nil region rfl rfl⟩
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
      let priorSpine := RelationJoinSnocSteps.ofList priorSteps
      let snocSpine := RelationJoinSnocSteps.snoc priorSpine step
      have snocTotal : ∀ snocOrigin : RelationJoinPrefixRegionOrigin
          (source := source) (dying := dying) (content := content)
          snocSpine.toList, ∃ target, PrefixRegionLands snocSpine
            (RelationJoinSemanticTrace.snoc (canonicalSpineAgreement trace) step
              rfl (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
                (by rfl)) snocOrigin target := by
        intro snocOrigin
        cases snocOrigin with
        | inl region =>
            obtain ⟨prior, landing⟩ := induction (.inl region)
            refine ⟨step.checkedPriorRegion prior, ?_⟩
            exact PrefixRegionLands.snoc_prior
              (canonicalSpineAgreement trace) step rfl (by rfl) (by rfl)
                (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) landing
                rfl rfl
        | inr occurrence =>
            rcases occurrence with ⟨occurrence, region⟩
            let occurrence' : Fin (priorSpine.toList.length + 1) :=
              Fin.cast (by
                simp only [snocSpine, RelationJoinSnocSteps.toList,
                  List.length_append, List.length_singleton]) occurrence
            refine Fin.lastCases
              (motive := fun index => ∃ target, PrefixRegionLands snocSpine _
                (.inr ⟨Fin.cast (by
                  simp only [snocSpine, RelationJoinSnocSteps.toList,
                    List.length_append, List.length_singleton]) index, region⟩)
                target)
              ?_ ?_ occurrence'
            · refine ⟨step.checkedFragmentRegion region.1, ?_⟩
              exact PrefixRegionLands.snoc_fresh
                (canonicalSpineAgreement trace) step rfl (by rfl) (by rfl)
                  (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) region rfl rfl
            · intro priorOccurrence
              obtain ⟨prior, landing⟩ :=
                induction (.inr ⟨priorOccurrence, region⟩)
              refine ⟨step.checkedPriorRegion prior, ?_⟩
              exact PrefixRegionLands.snoc_prior
                (canonicalSpineAgreement trace) step rfl (by rfl) (by rfl)
                  (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) landing
                  (by
                    apply congrArg Sum.inr
                    apply Sigma.ext
                    apply Fin.ext
                    rfl
                    exact HEq.rfl)
                  rfl
      exact PrefixRegionLands.total_reindex
        (RelationJoinSnocSteps.ofList_append_singleton priorSteps step).symm
        snocTotal origin

/-- A construction prefix has at most one landing for each neutral region
origin.  The visible spine makes nil/snoc inversion structural; the remaining
cases are exactly the splice construction's retained/fresh separation and
injectivity receipts. -/
theorem prefixRegionLands_functional
    {args : List Sig}
    {spine : RelationJoinSnocSteps (source := source) (dying := dying)
      (content := content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    {agreement : RelationJoinSemanticTrace source dying content parameters args
      spine.toList final finalRegionImage finalNodeImage finalWireImage
        finalDying finalScope}
    {origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) spine.toList}
    {left right : final.val.RegionId}
    (leftLanding : PrefixRegionLands spine agreement origin left)
    (rightLanding : PrefixRegionLands spine agreement origin right) :
    left = right := by
  induction leftLanding with
  | nil region leftOriginExact leftTargetExact =>
      cases rightLanding with
      | nil region' rightOriginExact rightTargetExact =>
          have regionExact : region = region' := by
            exact Sum.inl.inj (leftOriginExact.symm.trans rightOriginExact)
          exact leftTargetExact.trans (regionExact.trans rightTargetExact.symm)
  | snoc_prior trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact landing leftOriginExact leftTargetExact induction =>
      cases rightLanding with
      | snoc_prior trace' step' priorExact' priorRegionImageExact'
          priorNodeImageExact' priorWireImageExact' priorDyingExact'
          priorScopeExact' relationArgsExact' sourceParametersExact'
          landing' rightOriginExact rightTargetExact =>
          have priorOriginExact := prefixRegionOriginLift_injective step
            (leftOriginExact.symm.trans rightOriginExact)
          cases priorOriginExact
          subst_vars
          have traceExact : trace = trace' := Subsingleton.elim _ _
          cases traceExact
          exact congrArg step.checkedPriorRegion (induction landing')
      | snoc_fresh trace' step' priorExact' priorRegionImageExact'
          priorNodeImageExact' priorWireImageExact' priorDyingExact'
          priorScopeExact' relationArgsExact' sourceParametersExact' region
          rightOriginExact rightTargetExact =>
          exact (prefixRegionOriginLift_ne_fresh step _ region
            (leftOriginExact.symm.trans rightOriginExact)).elim
  | snoc_fresh trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact region leftOriginExact leftTargetExact =>
      cases rightLanding with
      | snoc_prior trace' step' priorExact' priorRegionImageExact'
          priorNodeImageExact' priorWireImageExact' priorDyingExact'
          priorScopeExact' relationArgsExact' sourceParametersExact'
          landing' rightOriginExact rightTargetExact =>
          exact (prefixRegionOriginLift_ne_fresh step _ region
            (rightOriginExact.symm.trans leftOriginExact)).elim
      | snoc_fresh trace' step' priorExact' priorRegionImageExact'
          priorNodeImageExact' priorWireImageExact' priorDyingExact'
          priorScopeExact' relationArgsExact' sourceParametersExact' region'
          rightOriginExact rightTargetExact =>
          have regionExact := prefixRegionFreshOrigin_injective step
            (leftOriginExact.symm.trans rightOriginExact)
          cases regionExact
          exact leftTargetExact.trans rightTargetExact.symm

/-- Two neutral origins cannot land on the same prefix region.  Structural
inversion exposes the last construction step; its retained/fresh injectivity
and separation receipts discharge the three snoc comparisons. -/
theorem prefixRegionLands_injective
    {args : List Sig}
    {spine : RelationJoinSnocSteps (source := source) (dying := dying)
      (content := content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    {agreement : RelationJoinSemanticTrace source dying content parameters args
      spine.toList final finalRegionImage finalNodeImage finalWireImage
        finalDying finalScope}
    {leftOrigin rightOrigin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) spine.toList}
    {target : final.val.RegionId}
    (leftLanding : PrefixRegionLands spine agreement leftOrigin target)
    (rightLanding : PrefixRegionLands spine agreement rightOrigin target) :
    leftOrigin = rightOrigin := by
  induction leftLanding with
  | nil region leftOriginExact leftTargetExact =>
      cases rightLanding with
      | nil region' rightOriginExact rightTargetExact =>
          have regionExact : region = region' :=
            leftTargetExact.symm.trans rightTargetExact
          exact leftOriginExact.trans
            ((congrArg Sum.inl regionExact).trans rightOriginExact.symm)
  | snoc_prior trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact landing leftOriginExact leftTargetExact induction =>
      cases rightLanding with
      | snoc_prior trace' step' priorExact' priorRegionImageExact'
          priorNodeImageExact' priorWireImageExact' priorDyingExact'
          priorScopeExact' relationArgsExact' sourceParametersExact'
          landing' rightOriginExact rightTargetExact =>
          cases priorExact
          cases priorExact'
          cases eq_of_heq priorRegionImageExact
          cases eq_of_heq priorNodeImageExact
          cases eq_of_heq priorWireImageExact
          cases eq_of_heq priorDyingExact
          cases eq_of_heq priorScopeExact
          cases eq_of_heq priorRegionImageExact'
          cases eq_of_heq priorNodeImageExact'
          cases eq_of_heq priorWireImageExact'
          cases eq_of_heq priorDyingExact'
          cases eq_of_heq priorScopeExact'
          have traceExact : trace = trace' := Subsingleton.elim _ _
          cases traceExact
          have priorTargetExact := step.checkedPriorRegion_injective
            (leftTargetExact.symm.trans rightTargetExact)
          cases priorTargetExact
          have priorOriginExact := induction landing'
          exact leftOriginExact.trans
            ((congrArg (prefixRegionOriginLift step) priorOriginExact).trans
              rightOriginExact.symm)
      | snoc_fresh trace' step' priorExact' priorRegionImageExact'
          priorNodeImageExact' priorWireImageExact' priorDyingExact'
          priorScopeExact' relationArgsExact' sourceParametersExact' region
          rightOriginExact rightTargetExact =>
          have collision : step.checkedFragmentRegion region.1 =
              step.checkedPriorRegion (priorRegionCast step priorExact _) :=
            rightTargetExact.symm.trans leftTargetExact
          exact (step.checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
            region.1 region.2 _ collision).elim
  | snoc_fresh trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact region leftOriginExact leftTargetExact =>
      cases rightLanding with
      | snoc_prior trace' step' priorExact' priorRegionImageExact'
          priorNodeImageExact' priorWireImageExact' priorDyingExact'
          priorScopeExact' relationArgsExact' sourceParametersExact'
          landing' rightOriginExact rightTargetExact =>
          have collision : step.checkedFragmentRegion region.1 =
              step.checkedPriorRegion (priorRegionCast step priorExact' _) :=
            leftTargetExact.symm.trans rightTargetExact
          exact (step.checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
            region.1 region.2 _ collision).elim
      | snoc_fresh trace' step' priorExact' priorRegionImageExact'
          priorNodeImageExact' priorWireImageExact' priorDyingExact'
          priorScopeExact' relationArgsExact' sourceParametersExact' region'
          rightOriginExact rightTargetExact =>
          have regionValueExact :=
            step.checkedFragmentRegion_injective_of_nonroot region.2 region'.2
              (leftTargetExact.symm.trans rightTargetExact)
          have regionExact : region = region' := Subtype.ext regionValueExact
          exact leftOriginExact.trans
            ((congrArg (prefixRegionFreshOrigin step) regionExact).trans
              rightOriginExact.symm)

end ConcreteWireQuantifier.RelationJoinSemanticTrace

namespace ConcreteWireQuantifier.RelationJoinSemanticTrace

/-- Terminal raw-region landing: the prefix construction landing followed by
the exhausted-relation deletion's all-region transport. -/
def plainPrefixRegionLands
    (result : RelationJoinResult source dying content parameters)
  (origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content)
      (RelationJoinSnocSteps.ofList result.steps).toList)
    (target : result.plainFinal.val.RegionId) : Prop :=
  ∃ bound, PrefixRegionLands (RelationJoinSnocSteps.ofList result.steps)
      (canonicalSpineAgreement result.semantic_trace)
      origin bound ∧ target = result.plainBoundRegionImage bound

/-- Every raw neutral region origin survives terminal exhausted-wire deletion. -/
theorem plainPrefixRegionLands_total
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content)
      (RelationJoinSnocSteps.ofList result.steps).toList) :
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

/-- Terminal deletion preserves prefix functionality because its region image
is injective. -/
theorem plainPrefixRegionLands_functional
    (result : RelationJoinResult source dying content parameters)
    {origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content)
      (RelationJoinSnocSteps.ofList result.steps).toList}
    {left right : result.plainFinal.val.RegionId}
    (leftLanding : plainPrefixRegionLands result origin left)
    (rightLanding : plainPrefixRegionLands result origin right) :
    left = right := by
  obtain ⟨leftBound, leftPrefix, rfl⟩ := leftLanding
  obtain ⟨rightBound, rightPrefix, same⟩ := rightLanding
  rw [same]
  apply congrArg result.plainBoundRegionImage
  exact prefixRegionLands_functional leftPrefix rightPrefix

/-- Terminal raw-region landing remains injective because exhausted-wire
deletion's all-region transport is injective. -/
theorem plainPrefixRegionLands_injective
    (result : RelationJoinResult source dying content parameters)
    {leftOrigin rightOrigin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content)
      (RelationJoinSnocSteps.ofList result.steps).toList}
    {target : result.plainFinal.val.RegionId}
    (leftLanding : plainPrefixRegionLands result leftOrigin target)
    (rightLanding : plainPrefixRegionLands result rightOrigin target) :
    leftOrigin = rightOrigin := by
  obtain ⟨leftBound, leftPrefix, leftTargetExact⟩ := leftLanding
  obtain ⟨rightBound, rightPrefix, rightTargetExact⟩ := rightLanding
  have boundExact := result.plainBoundRegionImage_injective
    (leftTargetExact.symm.trans rightTargetExact)
  cases boundExact
  exact prefixRegionLands_injective leftPrefix rightPrefix

end ConcreteWireQuantifier.RelationJoinSemanticTrace

end RawRegionTrace

end MonolithicWireQuantifier

end VisualProof
