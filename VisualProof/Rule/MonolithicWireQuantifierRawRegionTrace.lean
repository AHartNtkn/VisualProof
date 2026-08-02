import VisualProof.Rule.MonolithicWireQuantifierRawRegionOrigin

namespace VisualProof

namespace MonolithicWireQuantifier

open _root_.VisualProof.ConcreteWireQuantifier

section RawRegionTrace

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

namespace ConcreteWireQuantifier.RelationJoinConstructionTrace

/-- Cast a prefix target back to the exact prior carrier owned by a checked
construction snoc. -/
def priorRegionCast
    {current : CheckedDiagram definitions}
    (step : RelationJoinStep source dying content)
    (priorExact : step.prior = current) :
    current.val.RegionId → step.prior.val.RegionId :=
  cast (congrArg (fun diagram : CheckedDiagram definitions =>
    diagram.val.RegionId) priorExact.symm)

/-- Construction-owned region landing defined by structural recursion on the
validated Type-valued construction trace. -/
def PrefixRegionLands {args : List Sig} :
    ∀ {steps : List (RelationJoinStep source dying content)}
      {final : CheckedDiagram definitions}
      {finalRegionImage : source.val.RegionId → final.val.RegionId}
      {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
      {finalWireImage : source.val.WireId → final.val.WireId}
      {finalDying : final.val.WireId} {finalScope : final.val.RegionId},
      RelationJoinConstructionTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope →
      RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps → final.val.RegionId → Prop
  | _, _, _, _, _, _, _, .nil, origin, target =>
      ∃ region : source.val.RegionId, origin = .inl region ∧ target = region
  | _, _, _, _, _, _, _,
      .snoc trace step priorExact _ _ _ _ _ _ _,
      origin, target =>
      (∃ priorOrigin priorTarget, PrefixRegionLands trace priorOrigin priorTarget ∧
        origin = prefixRegionOriginLift step priorOrigin ∧
        target = step.checkedPriorRegion
          (priorRegionCast step priorExact priorTarget)) ∨
      (∃ region : { region : content.val.diagram.RegionId //
          region ≠ content.val.diagram.root },
        origin = prefixRegionFreshOrigin step region ∧
        target = step.checkedFragmentRegion region.1)

theorem prefixRegionLands_source
    {args : List Sig}
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
    PrefixRegionLands trace (.inl region) (finalRegionImage region) := by
  induction trace with
  | nil => exact ⟨region, rfl, rfl⟩
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst_vars
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      exact Or.inl ⟨.inl region, _, induction, rfl, by
        rw [step.checkedRegionImage_eq_checkedPriorRegion]
        rfl⟩

theorem prefixRegionLands_last
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    {currentRegionImage : source.val.RegionId → current.val.RegionId}
    {currentNodeImage : source.val.NodeId → Option current.val.NodeId}
    {currentWireImage : source.val.WireId → current.val.WireId}
    {currentDying : current.val.WireId} {currentScope : current.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
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
      (.snoc trace step priorExact priorRegionImageExact priorNodeImageExact
        priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
        sourceParametersExact)
      (prefixRegionFreshOrigin step region)
      (step.checkedFragmentRegion region.1) :=
  Or.inr ⟨region, rfl, rfl⟩

theorem prefixRegionLands_total
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps) :
    ∃ target, PrefixRegionLands trace origin target := by
  induction trace with
  | nil =>
      cases origin with
      | inl region => exact ⟨region, region, rfl, rfl⟩
      | inr occurrence => exact Fin.elim0 occurrence.1
  | @snoc priorSteps current currentRegionImage currentNodeImage currentWireImage
      currentDying currentScope trace step priorExact priorRegionImageExact
      priorNodeImageExact priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact induction =>
      subst_vars
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases origin with
      | inl region =>
          obtain ⟨prior, landing⟩ := induction (.inl region)
          exact ⟨step.checkedPriorRegion prior,
            Or.inl ⟨.inl region, prior, landing, rfl, rfl⟩⟩
      | inr occurrence =>
          rcases occurrence with ⟨occurrence, region⟩
          let occurrence' : Fin (priorSteps.length + 1) :=
            Fin.cast (by simp) occurrence
          refine Fin.lastCases
            (motive := fun index => ∃ target, PrefixRegionLands _
              (.inr ⟨Fin.cast (by simp) index, region⟩) target)
            ?_ ?_ occurrence'
          · exact ⟨step.checkedFragmentRegion region.1,
              Or.inr ⟨region, rfl, rfl⟩⟩
          · intro priorOccurrence
            obtain ⟨prior, landing⟩ :=
              induction (.inr ⟨priorOccurrence, region⟩)
            refine ⟨step.checkedPriorRegion prior, ?_⟩
            exact Or.inl ⟨.inr ⟨priorOccurrence, region⟩, prior, landing,
              (by
                apply congrArg Sum.inr
                apply Sigma.ext
                apply Fin.ext
                rfl
                exact HEq.rfl),
              rfl⟩

theorem prefixRegionLands_functional
    {args : List Sig}
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
    {left right : final.val.RegionId}
    (leftLanding : PrefixRegionLands trace origin left)
    (rightLanding : PrefixRegionLands trace origin right) : left = right := by
  induction trace with
  | nil =>
      rcases leftLanding with ⟨region, leftOriginExact, leftTargetExact⟩
      rcases rightLanding with ⟨region', rightOriginExact, rightTargetExact⟩
      have regionExact : region = region' :=
        Sum.inl.inj (leftOriginExact.symm.trans rightOriginExact)
      exact leftTargetExact.trans (regionExact.trans rightTargetExact.symm)
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      rcases leftLanding with leftPrior | leftFresh
      · rcases leftPrior with
          ⟨leftOrigin, leftTarget, leftLanding, leftOriginExact,
            leftTargetExact⟩
        rcases rightLanding with rightPrior | rightFresh
        · rcases rightPrior with
            ⟨rightOrigin, rightTarget, rightLanding, rightOriginExact,
              rightTargetExact⟩
          have priorOriginExact := prefixRegionOriginLift_injective step
            (leftOriginExact.symm.trans rightOriginExact)
          cases priorOriginExact
          have priorTargetExact := induction leftLanding rightLanding
          exact leftTargetExact.trans
            ((congrArg (fun target => step.checkedPriorRegion
              (priorRegionCast step priorExact target)) priorTargetExact).trans
              rightTargetExact.symm)
        · rcases rightFresh with
            ⟨region, rightOriginExact, _rightTargetExact⟩
          exact (prefixRegionOriginLift_ne_fresh step _ region
            (leftOriginExact.symm.trans rightOriginExact)).elim
      · rcases leftFresh with ⟨region, leftOriginExact, _leftTargetExact⟩
        rcases rightLanding with rightPrior | rightFresh
        · rcases rightPrior with
            ⟨rightOrigin, _rightTarget, _rightLanding, rightOriginExact,
              _rightTargetExact⟩
          exact (prefixRegionOriginLift_ne_fresh step rightOrigin region
            (rightOriginExact.symm.trans leftOriginExact)).elim
        · rcases rightFresh with
            ⟨region', rightOriginExact, rightTargetExact⟩
          have regionExact := prefixRegionFreshOrigin_injective step
            (leftOriginExact.symm.trans rightOriginExact)
          cases regionExact
          exact _leftTargetExact.trans rightTargetExact.symm

theorem prefixRegionLands_injective
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    {trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope}
    {leftOrigin rightOrigin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) steps}
    {target : final.val.RegionId}
    (leftLanding : PrefixRegionLands trace leftOrigin target)
    (rightLanding : PrefixRegionLands trace rightOrigin target) :
    leftOrigin = rightOrigin := by
  induction trace with
  | nil =>
      rcases leftLanding with ⟨region, leftOriginExact, leftTargetExact⟩
      rcases rightLanding with ⟨region', rightOriginExact, rightTargetExact⟩
      have regionExact : region = region' :=
        leftTargetExact.symm.trans rightTargetExact
      exact leftOriginExact.trans
        ((congrArg Sum.inl regionExact).trans rightOriginExact.symm)
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      rcases leftLanding with leftPrior | leftFresh
      · rcases leftPrior with
          ⟨leftPriorOrigin, leftPriorTarget, leftLanding, leftOriginExact,
            leftTargetExact⟩
        rcases rightLanding with rightPrior | rightFresh
        · rcases rightPrior with
            ⟨rightPriorOrigin, rightPriorTarget, rightLanding,
              rightOriginExact, rightTargetExact⟩
          have castTargetExact := step.checkedPriorRegion_injective
            (leftTargetExact.symm.trans rightTargetExact)
          have priorTargetExact : leftPriorTarget = rightPriorTarget := by
            cases priorExact
            simpa [priorRegionCast] using castTargetExact
          cases priorTargetExact
          have priorOriginExact := induction leftLanding rightLanding
          exact leftOriginExact.trans
            ((congrArg (prefixRegionOriginLift step) priorOriginExact).trans
              rightOriginExact.symm)
        · rcases rightFresh with
            ⟨region, _rightOriginExact, rightTargetExact⟩
          have collision : step.checkedFragmentRegion region.1 =
              step.checkedPriorRegion
                (priorRegionCast step priorExact leftPriorTarget) :=
            rightTargetExact.symm.trans leftTargetExact
          exact (step.checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
            region.1 region.2 _ collision).elim
      · rcases leftFresh with
          ⟨region, leftOriginExact, leftTargetExact⟩
        rcases rightLanding with rightPrior | rightFresh
        · rcases rightPrior with
            ⟨_rightPriorOrigin, rightPriorTarget, _rightLanding,
              _rightOriginExact, rightTargetExact⟩
          have collision : step.checkedFragmentRegion region.1 =
              step.checkedPriorRegion
                (priorRegionCast step priorExact rightPriorTarget) :=
            leftTargetExact.symm.trans rightTargetExact
          exact (step.checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
            region.1 region.2 _ collision).elim
        · rcases rightFresh with
            ⟨region', rightOriginExact, rightTargetExact⟩
          have regionValueExact :=
            step.checkedFragmentRegion_injective_of_nonroot region.2 region'.2
              (leftTargetExact.symm.trans rightTargetExact)
          have regionExact : region = region' := Subtype.ext regionValueExact
          exact leftOriginExact.trans
            ((congrArg (prefixRegionFreshOrigin step) regionExact).trans
              rightOriginExact.symm)

end ConcreteWireQuantifier.RelationJoinConstructionTrace

namespace ConcreteWireQuantifier.RelationJoinConstructionTrace

def plainPrefixRegionLands
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) result.steps)
    (target : result.plainFinal.val.RegionId) : Prop :=
  ∃ bound, PrefixRegionLands result.construction_trace origin bound ∧
    target = result.plainBoundRegionImage bound

theorem plainPrefixRegionLands_total
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) result.steps) :
    ∃ target, plainPrefixRegionLands result origin target := by
  obtain ⟨bound, landing⟩ := prefixRegionLands_total
    result.construction_trace origin
  exact ⟨result.plainBoundRegionImage bound, bound, landing, rfl⟩

theorem plainPrefixRegionLands_source
    (result : RelationJoinResult source dying content parameters)
    (region : source.val.RegionId) :
    plainPrefixRegionLands result (.inl region)
      (result.plainBoundRegionImage (result.boundRegionImage region)) := by
  refine ⟨result.boundRegionImage region, ?_, rfl⟩
  exact prefixRegionLands_source result.construction_trace region

theorem plainPrefixRegionLands_functional
    (result : RelationJoinResult source dying content parameters)
    {origin : RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) result.steps}
    {left right : result.plainFinal.val.RegionId}
    (leftLanding : plainPrefixRegionLands result origin left)
    (rightLanding : plainPrefixRegionLands result origin right) : left = right := by
  obtain ⟨leftBound, leftPrefix, rfl⟩ := leftLanding
  obtain ⟨rightBound, rightPrefix, same⟩ := rightLanding
  rw [same]
  exact congrArg result.plainBoundRegionImage
    (prefixRegionLands_functional leftPrefix rightPrefix)

theorem plainPrefixRegionLands_injective
    (result : RelationJoinResult source dying content parameters)
    {leftOrigin rightOrigin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) result.steps}
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

end ConcreteWireQuantifier.RelationJoinConstructionTrace

end RawRegionTrace

end MonolithicWireQuantifier

end VisualProof
