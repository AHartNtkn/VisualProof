import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawWireOrigins
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawOriginFacts

namespace VisualProof

namespace ConcreteWireQuantifier

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}

/-- The content wire allocated by an internal construction-wire origin. -/
def ConstructionWireOrigin.contentWire :
    {steps : List (RelationJoinStep source dying content)} →
      ConstructionWireOrigin steps → content.val.diagram.WireId
  | step :: _, .head position =>
      step.attachment.fragmentInternalWires.get position
  | _ :: _, .tail origin => origin.contentWire

/-- The source construction occurrence that allocated an internal wire. -/
def ConstructionWireOrigin.step :
    {steps : List (RelationJoinStep source dying content)} →
      ConstructionWireOrigin steps → RelationJoinStep source dying content
  | step :: _, .head _ => step
  | _ :: _, .tail origin => origin.step

/-- Lift an established internal-wire origin through a newest snoc step. -/
def liftConstructionWireOrigin
    (step : RelationJoinStep source dying content) :
    {steps : List (RelationJoinStep source dying content)} →
      ConstructionWireOrigin steps → ConstructionWireOrigin (steps ++ [step])
  | [], origin => nomatch origin
  | _ :: _, .head position => .head position
  | _ :: _, .tail origin => .tail (liftConstructionWireOrigin step origin)

/-- Introduce an internal-wire origin at the newest snoc occurrence. -/
def freshConstructionWireOrigin :
    (steps : List (RelationJoinStep source dying content)) →
      (step : RelationJoinStep source dying content) →
      Fin step.attachment.fragmentInternalWires.length →
      ConstructionWireOrigin (steps ++ [step])
  | [], _, position => .head position
  | _ :: rest, step, position =>
      .tail (freshConstructionWireOrigin rest step position)

theorem constructionWireOriginRows_snoc
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content) :
    constructionWireOriginRows (steps ++ [step]) =
      (constructionWireOriginRows steps).map
          (liftConstructionWireOrigin step) ++
        (Data.Finite.allFin
          step.attachment.fragmentInternalWires.length).map
            (freshConstructionWireOrigin steps step) := by
  induction steps with
  | nil =>
      simp only [List.nil_append, constructionWireOriginRows, List.map_nil,
        liftConstructionWireOrigin, freshConstructionWireOrigin,
        List.append_nil]
      have mapped :
          (Data.Finite.allFin
              step.attachment.fragmentInternalWires.length).map
              (ConstructionWireOrigin.head :
                Fin step.attachment.fragmentInternalWires.length →
                  ConstructionWireOrigin [step]) =
            (Data.Finite.allFin
              step.attachment.fragmentInternalWires.length).map
              (fun position :
                Fin step.attachment.fragmentInternalWires.length =>
                  (ConstructionWireOrigin.head position :
                    ConstructionWireOrigin [step])) := by
        apply List.map_congr_left
        intro position _
        rfl
      exact mapped.trans (List.nil_append _).symm
  | cons head rest induction =>
      simp only [List.cons_append, constructionWireOriginRows, induction,
        liftConstructionWireOrigin, freshConstructionWireOrigin,
        List.map_append, List.map_map, Function.comp_apply]
      let first : List (ConstructionWireOrigin (head :: (rest ++ [step]))) :=
        (Data.Finite.allFin
          head.attachment.fragmentInternalWires.length).map
            (fun position => ConstructionWireOrigin.head position)
      let retained : List
          (ConstructionWireOrigin (head :: (rest ++ [step]))) :=
        (constructionWireOriginRows rest).map
          (fun origin => ConstructionWireOrigin.tail
            (liftConstructionWireOrigin step origin))
      let fresh : List
          (ConstructionWireOrigin (head :: (rest ++ [step]))) :=
        (Data.Finite.allFin
          step.attachment.fragmentInternalWires.length).map
            (fun position => ConstructionWireOrigin.tail
              (freshConstructionWireOrigin rest step position))
      change first ++ (retained ++ fresh) = (first ++ retained) ++ fresh
      exact (List.append_assoc first retained fresh).symm

@[simp] theorem ConstructionWireOrigin.contentWire_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : ConstructionWireOrigin steps) :
    (liftConstructionWireOrigin step origin).contentWire =
      origin.contentWire := by
  induction steps with
  | nil => exact nomatch origin
  | cons head rest induction =>
      cases origin with
      | head position => rfl
      | tail origin => exact induction origin

@[simp] theorem ConstructionWireOrigin.contentWire_fresh
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (position : Fin step.attachment.fragmentInternalWires.length) :
    (freshConstructionWireOrigin steps step position).contentWire =
      step.attachment.fragmentInternalWires.get position := by
  induction steps with
  | nil => rfl
  | cons head rest induction => exact induction

/-- The signature carried intrinsically by a terminal raw wire origin. -/
def expectedFinalWireSignature
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters) :
    FinalWireOrigin result → Sig
  | .inl wire => (source.val.wires wire.1).sig
  | .inr origin =>
      (content.val.diagram.wires origin.contentWire).sig

/-- Lift a prefix region origin through a leading construction occurrence. -/
def consLiftRegionOrigin
    (step : RelationJoinStep source dying content)
    {steps : List (RelationJoinStep source dying content)} :
    PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps →
    PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (step :: steps)
  | .inl region => .inl region
  | .inr ⟨occurrence, region⟩ => .inr ⟨Fin.succ occurrence, region⟩

/-- The exact construction-owned scope of an internal wire origin. -/
def ConstructionWireOrigin.scopeOrigin :
    {steps : List (RelationJoinStep source dying content)} →
      (origin : ConstructionWireOrigin steps) →
      PrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps
  | step :: _, .head position =>
      let scope :=
        (content.val.diagram.wires
          (step.attachment.fragmentInternalWires.get position)).scope
      if root : scope = content.val.diagram.root then
        .inl step.sourceRegion
      else
        .inr ⟨0, ⟨scope, root⟩⟩
  | step :: _, .tail origin => consLiftRegionOrigin step origin.scopeOrigin

@[simp] theorem ConstructionWireOrigin.scopeOrigin_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : ConstructionWireOrigin steps) :
    (liftConstructionWireOrigin step origin).scopeOrigin =
      liftRegionOrigin step origin.scopeOrigin := by
  induction steps with
  | nil => exact nomatch origin
  | cons head rest induction =>
      cases origin with
      | head position =>
          let scope := (content.val.diagram.wires
            (head.attachment.fragmentInternalWires.get position)).scope
          change
            (if root : scope = content.val.diagram.root then
              .inl head.sourceRegion
            else .inr ⟨(⟨0, by simp⟩ : Fin ((head :: rest) ++ [step]).length),
              ⟨scope, root⟩⟩) =
              liftRegionOrigin step
                (if root : scope = content.val.diagram.root then
                  .inl head.sourceRegion
                else .inr ⟨(⟨0, by simp⟩ : Fin (head :: rest).length),
                  ⟨scope, root⟩⟩)
          by_cases root : scope = content.val.diagram.root
          · simp [scope, root, liftRegionOrigin]
          · simp only [root, dite_false, liftRegionOrigin]
            congr 2
      | tail origin =>
          change consLiftRegionOrigin head
              (liftConstructionWireOrigin step origin).scopeOrigin =
            liftRegionOrigin step
              (consLiftRegionOrigin head origin.scopeOrigin)
          rw [induction origin]
          cases scopeExact : origin.scopeOrigin with
          | inl region => rfl
          | inr occurrence =>
              rcases occurrence with ⟨index, region⟩
              simp only [liftRegionOrigin, consLiftRegionOrigin]
              congr 2

@[simp] theorem ConstructionWireOrigin.scopeOrigin_fresh
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (position : Fin step.attachment.fragmentInternalWires.length) :
    (freshConstructionWireOrigin steps step position).scopeOrigin =
      let scope := (content.val.diagram.wires
        (step.attachment.fragmentInternalWires.get position)).scope
      if root : scope = content.val.diagram.root then
        .inl step.sourceRegion
      else
        freshRegionOrigin step ⟨scope, root⟩ := by
  induction steps with
  | nil => rfl
  | cons head rest induction =>
      change consLiftRegionOrigin head
          (freshConstructionWireOrigin rest step position).scopeOrigin = _
      rw [induction]
      let scope := (content.val.diagram.wires
        (step.attachment.fragmentInternalWires.get position)).scope
      change consLiftRegionOrigin head
          (if root : scope = content.val.diagram.root then
            .inl step.sourceRegion
          else freshRegionOrigin (steps := rest) step ⟨scope, root⟩) =
        (if root : scope = content.val.diagram.root then
          .inl step.sourceRegion
        else freshRegionOrigin (steps := head :: rest) step ⟨scope, root⟩)
      by_cases root : scope = content.val.diagram.root
      · simp [root, consLiftRegionOrigin]
      · simp only [root, dite_false, consLiftRegionOrigin,
          freshRegionOrigin]
        congr 2

/-- The region origin carrying a terminal raw wire origin. -/
def expectedFinalWireScope
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters) :
    FinalWireOrigin result → RelationJoinResult.FinalRegionOrigin result
  | .inl wire => .inl (source.val.wires wire.1).scope
  | .inr origin => origin.scopeOrigin

/-- The construction-order origin occupying one bound wire target. -/
def RelationJoinConstructionTrace.boundWireOrigin
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying finalScope)
    (target : final.val.WireId) :
    source.val.WireId ⊕ ConstructionWireOrigin steps :=
  Fin.addCases Sum.inl
    (fun position => Sum.inr ((constructionWireOriginRows steps).get position))
    (Fin.cast (by
      rw [trace.boundWireCount_exact]) target)

/-- Intrinsic signature of one bound construction wire origin. -/
def boundWireOriginSignature
    {steps : List (RelationJoinStep source dying content)} :
    source.val.WireId ⊕ ConstructionWireOrigin steps → Sig
  | .inl wire => (source.val.wires wire).sig
  | .inr origin => (content.val.diagram.wires origin.contentWire).sig

/-- Intrinsic region origin carrying one bound construction wire origin. -/
def boundWireOriginScope
    {steps : List (RelationJoinStep source dying content)} :
    source.val.WireId ⊕ ConstructionWireOrigin steps →
      PrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps
  | .inl wire => .inl (source.val.wires wire).scope
  | .inr origin => origin.scopeOrigin

/-- Lift both classes of bound wire origins through one newest step. -/
def liftBoundWireOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    source.val.WireId ⊕ ConstructionWireOrigin steps →
      source.val.WireId ⊕ ConstructionWireOrigin (steps ++ [step])
  | .inl wire => .inl wire
  | .inr origin => .inr (liftConstructionWireOrigin step origin)

@[simp] theorem boundWireOriginSignature_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : source.val.WireId ⊕ ConstructionWireOrigin steps) :
    boundWireOriginSignature (liftBoundWireOrigin step origin) =
      boundWireOriginSignature origin := by
  cases origin <;> simp [liftBoundWireOrigin, boundWireOriginSignature]

@[simp] theorem boundWireOriginScope_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : source.val.WireId ⊕ ConstructionWireOrigin steps) :
    boundWireOriginScope (liftBoundWireOrigin step origin) =
      liftRegionOrigin step (boundWireOriginScope origin) := by
  cases origin <;>
    simp [liftBoundWireOrigin, boundWireOriginScope, liftRegionOrigin]

theorem RelationJoinConstructionTrace.boundWireOrigin_checkedPrior
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    {priorAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior}
    {currentWireImage : source.val.WireId → step.prior.val.WireId}
    {currentDying : step.prior.val.WireId}
    {currentScope : step.prior.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps step.prior priorAtlas currentWireImage currentDying currentScope)
    (priorWireImageExact : HEq step.priorWireImage currentWireImage)
    (priorDyingExact : HEq (step.priorWireImage dying) currentDying)
    (priorScopeExact : HEq
      (priorAtlas.regionImage (source.val.wires dying).scope) currentScope)
    (relationArgsExact : step.relationArgs = args)
    (sourceParametersExact : step.sourceParameters = parameters)
    (receipt : AtlasStepReceipt step priorAtlas)
    (applicationLanding : NodeLands priorAtlas.rows (.inl step.application)
      step.priorApplication)
    (target : step.prior.val.WireId) :
    (RelationJoinConstructionTrace.snoc step trace priorWireImageExact
      priorDyingExact priorScopeExact relationArgsExact sourceParametersExact
      receipt applicationLanding).boundWireOrigin
        (step.checkedPriorWire target) =
      liftBoundWireOrigin step (trace.boundWireOrigin target) := by
  let oldSplit : Fin
      (source.val.wireCount + (constructionWireOriginRows steps).length) :=
    Fin.cast (trace.boundWireCount_exact) target
  have targetExact :
      target = Fin.cast trace.boundWireCount_exact.symm oldSplit := by
    apply Fin.ext
    rfl
  rw [targetExact]
  refine Fin.addCases (motive := fun oldSplit =>
    (RelationJoinConstructionTrace.snoc step trace priorWireImageExact
      priorDyingExact priorScopeExact relationArgsExact sourceParametersExact
      receipt applicationLanding).boundWireOrigin
        (step.checkedPriorWire
          (Fin.cast trace.boundWireCount_exact.symm oldSplit)) =
      liftBoundWireOrigin step
        (trace.boundWireOrigin
          (Fin.cast trace.boundWireCount_exact.symm oldSplit))) ?_ ?_ oldSplit
  · intro sourceWire
    unfold RelationJoinConstructionTrace.boundWireOrigin
    have oldCast :
        Fin.cast trace.boundWireCount_exact
            (Fin.cast trace.boundWireCount_exact.symm
              (Fin.castAdd (constructionWireOriginRows steps).length
                sourceWire)) =
          Fin.castAdd (constructionWireOriginRows steps).length sourceWire := by
      apply Fin.ext
      rfl
    have newCast :
        Fin.cast
            (RelationJoinConstructionTrace.boundWireCount_exact
              (RelationJoinConstructionTrace.snoc step trace
                priorWireImageExact priorDyingExact priorScopeExact
                relationArgsExact sourceParametersExact receipt
                applicationLanding))
            (step.checkedPriorWire
              (Fin.cast trace.boundWireCount_exact.symm
                (Fin.castAdd (constructionWireOriginRows steps).length
                  sourceWire))) =
          Fin.castAdd (constructionWireOriginRows (steps ++ [step])).length
            sourceWire := by
      apply Fin.ext
      simp only [step.checkedPriorWire_val, Fin.val_cast,
        Fin.val_castAdd]
    rw [oldCast, newCast, Fin.addCases_left, Fin.addCases_left]
    rfl
  · intro position
    unfold RelationJoinConstructionTrace.boundWireOrigin
    let extendedPosition : Fin
        (constructionWireOriginRows (steps ++ [step])).length :=
      Fin.cast (by
        rw [constructionWireOriginRows_snoc]
        simp) (Fin.castAdd
          (Data.Finite.allFin
            step.attachment.fragmentInternalWires.length).length position)
    have oldCast :
        Fin.cast trace.boundWireCount_exact
            (Fin.cast trace.boundWireCount_exact.symm
              (Fin.natAdd source.val.wireCount position)) =
          Fin.natAdd source.val.wireCount position := by
      apply Fin.ext
      rfl
    have newCast :
        Fin.cast
            (RelationJoinConstructionTrace.boundWireCount_exact
              (RelationJoinConstructionTrace.snoc step trace
                priorWireImageExact priorDyingExact priorScopeExact
                relationArgsExact sourceParametersExact receipt
                applicationLanding))
            (step.checkedPriorWire
              (Fin.cast trace.boundWireCount_exact.symm
                (Fin.natAdd source.val.wireCount position))) =
          Fin.natAdd source.val.wireCount extendedPosition := by
      apply Fin.ext
      simp only [step.checkedPriorWire_val, Fin.val_cast, Fin.val_natAdd,
        Fin.val_castAdd, extendedPosition]
    rw [oldCast, newCast, Fin.addCases_right, Fin.addCases_right]
    apply congrArg Sum.inr
    rw [List.get_of_eq (constructionWireOriginRows_snoc steps step)
      extendedPosition]
    simp [extendedPosition, List.get_eq_getElem]

theorem RelationJoinConstructionTrace.boundWireOrigin_fresh
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    {priorAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior}
    {currentWireImage : source.val.WireId → step.prior.val.WireId}
    {currentDying : step.prior.val.WireId}
    {currentScope : step.prior.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps step.prior priorAtlas currentWireImage currentDying currentScope)
    (priorWireImageExact : HEq step.priorWireImage currentWireImage)
    (priorDyingExact : HEq (step.priorWireImage dying) currentDying)
    (priorScopeExact : HEq
      (priorAtlas.regionImage (source.val.wires dying).scope) currentScope)
    (relationArgsExact : step.relationArgs = args)
    (sourceParametersExact : step.sourceParameters = parameters)
    (receipt : AtlasStepReceipt step priorAtlas)
    (applicationLanding : NodeLands priorAtlas.rows (.inl step.application)
      step.priorApplication)
    (position : Fin step.attachment.fragmentInternalWires.length) :
    (RelationJoinConstructionTrace.snoc step trace priorWireImageExact
      priorDyingExact priorScopeExact relationArgsExact sourceParametersExact
      receipt applicationLanding).boundWireOrigin
        (Internal.checkedWire step.generated
          (step.attachment.freshWire position)) =
      .inr (freshConstructionWireOrigin steps step position) := by
  let localPosition : Fin
      (Data.Finite.allFin
        step.attachment.fragmentInternalWires.length).length :=
    Fin.cast (by simp [Data.Finite.allFin_eq_finRange]) position
  let extendedPosition : Fin
      (constructionWireOriginRows (steps ++ [step])).length :=
    Fin.cast (by
      rw [constructionWireOriginRows_snoc]
      simp) (Fin.natAdd (constructionWireOriginRows steps).length localPosition)
  have baseCount :
      step.base.val.wireCount = step.prior.val.wireCount := by
    rw [step.baseGenerated]
    simp [ConcreteDiagram.DenseErasure.eraseNodeCandidate,
      Internal.retainedWires, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange]
  have targetCast :
      Fin.cast
          (RelationJoinConstructionTrace.boundWireCount_exact
            (RelationJoinConstructionTrace.snoc step trace
              priorWireImageExact priorDyingExact priorScopeExact
              relationArgsExact sourceParametersExact receipt
              applicationLanding))
          (Internal.checkedWire step.generated
            (step.attachment.freshWire position)) =
        Fin.natAdd source.val.wireCount extendedPosition := by
    apply Fin.ext
    simp [Internal.checkedWire, ConcreteSpliceAttachment.freshWire,
      extendedPosition, localPosition, baseCount,
      trace.boundWireCount_exact]
    omega
  unfold RelationJoinConstructionTrace.boundWireOrigin
  rw [targetCast, Fin.addCases_right]
  apply congrArg Sum.inr
  rw [List.get_of_eq (constructionWireOriginRows_snoc steps step)
    extendedPosition]
  simp [extendedPosition, localPosition, List.get_eq_getElem,
    Data.Finite.allFin_eq_finRange]

/-- Every bound raw wire has the signature named by its construction origin. -/
theorem RelationJoinConstructionTrace.boundWire_signature_exact
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying finalScope)
    (target : final.val.WireId) :
    (final.val.wires target).sig =
      boundWireOriginSignature (trace.boundWireOrigin target) := by
  induction trace with
  | nil =>
      unfold RelationJoinConstructionTrace.boundWireOrigin
      generalize splitExact : Fin.cast _ target = splitTarget
      have splitTargetExact : splitTarget = Fin.castAdd 0 target := by
        apply Fin.ext
        simpa using (congrArg Fin.val splitExact).symm
      rw [splitTargetExact]
      let right : Fin 0 →
          source.val.WireId ⊕ ConstructionWireOrigin
            (source := source) (dying := dying) (content := content) [] :=
        fun position => Sum.inr
          ((constructionWireOriginRows (source := source) (dying := dying)
            (content := content) []).get position)
      have originExact :
          Fin.addCases (motive := fun _ =>
              source.val.WireId ⊕ ConstructionWireOrigin
                (source := source) (dying := dying) (content := content) [])
              (fun wire => Sum.inl wire) right
              (Fin.castAdd 0 target) =
            (Sum.inl target : source.val.WireId ⊕ ConstructionWireOrigin
              (source := source) (dying := dying) (content := content) []) :=
        Fin.addCases_left target
      change (source.val.wires target).sig =
        boundWireOriginSignature
          (Fin.addCases (motive := fun _ =>
              source.val.WireId ⊕ ConstructionWireOrigin
                (source := source) (dying := dying) (content := content) [])
            (fun wire => Sum.inl wire) right (Fin.castAdd 0 target))
      rw [originExact]
      rfl
  | @snoc steps step priorAtlas currentWireImage currentDying currentScope
      trace priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact receipt applicationLanding
      induction =>
      let splitTarget : Fin
          (step.prior.val.wireCount +
            step.attachment.fragmentInternalWires.length) :=
        Fin.cast step.checked_wireCount target
      have targetExact :
          target = Fin.cast step.checked_wireCount.symm splitTarget := by
        apply Fin.ext
        rfl
      rw [targetExact]
      refine Fin.addCases (motive := fun splitTarget =>
        (step.checked.val.wires
          (Fin.cast step.checked_wireCount.symm splitTarget)).sig =
        boundWireOriginSignature
          ((RelationJoinConstructionTrace.snoc step trace priorWireImageExact
            priorDyingExact priorScopeExact relationArgsExact
            sourceParametersExact receipt applicationLanding).boundWireOrigin
              (Fin.cast step.checked_wireCount.symm splitTarget))) ?_ ?_
          splitTarget
      · intro priorTarget
        have checkedTarget :
            Fin.cast step.checked_wireCount.symm
                (Fin.castAdd step.attachment.fragmentInternalWires.length
                  priorTarget) =
              step.checkedPriorWire priorTarget := by
          apply Fin.ext
          rfl
        rw [checkedTarget, step.checkedPriorWire_signature,
          induction priorTarget]
        rw [(trace.boundWireOrigin_checkedPrior step priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact
          sourceParametersExact receipt applicationLanding priorTarget)]
        exact (boundWireOriginSignature_lift step
          (trace.boundWireOrigin priorTarget)).symm
      · intro fresh
        have checkedTarget :
            Fin.cast step.checked_wireCount.symm
                (Fin.natAdd step.prior.val.wireCount fresh) =
              Internal.checkedWire step.generated
                (step.attachment.freshWire fresh) := by
          have baseCount :
              step.base.val.wireCount = step.prior.val.wireCount := by
            rw [step.baseGenerated]
            simp [ConcreteDiagram.DenseErasure.eraseNodeCandidate,
              Internal.retainedWires, ConcreteDiagram.wiresList,
              Data.Finite.allFin_eq_finRange]
          apply Fin.ext
          simp [Internal.checkedWire, ConcreteSpliceAttachment.freshWire,
            baseCount]
        rw [checkedTarget, Internal.checkedWire_signature_transport,
          ConcreteSpliceAttachment.diagram_wire_freshWire]
        rw [trace.boundWireOrigin_fresh step priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact
          sourceParametersExact receipt applicationLanding fresh]
        simp [boundWireOriginSignature]

/-- Every bound raw wire has the scope named by its construction origin. -/
theorem RelationJoinConstructionTrace.boundWire_scope_exact
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying finalScope)
    (target : final.val.WireId) :
    finalAtlas.rows.regionAt (final.val.wires target).scope =
      boundWireOriginScope (trace.boundWireOrigin target) := by
  induction trace with
  | nil =>
      unfold RelationJoinConstructionTrace.boundWireOrigin
      generalize splitExact : Fin.cast _ target = splitTarget
      have splitTargetExact : splitTarget = Fin.castAdd 0 target := by
        apply Fin.ext
        simpa using (congrArg Fin.val splitExact).symm
      rw [splitTargetExact]
      let right : Fin 0 →
          source.val.WireId ⊕ ConstructionWireOrigin
            (source := source) (dying := dying) (content := content) [] :=
        fun position => Sum.inr
          ((constructionWireOriginRows (source := source) (dying := dying)
            (content := content) []).get position)
      have originExact :
          Fin.addCases (motive := fun _ =>
              source.val.WireId ⊕ ConstructionWireOrigin
                (source := source) (dying := dying) (content := content) [])
              (fun wire => Sum.inl wire) right
              (Fin.castAdd 0 target) =
            (Sum.inl target : source.val.WireId ⊕ ConstructionWireOrigin
              (source := source) (dying := dying) (content := content) []) :=
        Fin.addCases_left target
      change initialAtlas.rows.regionAt (source.val.wires target).scope =
        boundWireOriginScope
          (Fin.addCases (motive := fun _ =>
              source.val.WireId ⊕ ConstructionWireOrigin
                (source := source) (dying := dying) (content := content) [])
            (fun wire => Sum.inl wire) right (Fin.castAdd 0 target))
      rw [originExact]
      change (initialRows (source := source) (dying := dying)
          (content := content)).regionAt (source.val.wires target).scope =
        .inl (source.val.wires target).scope
      exact initialRows_regionAt (source.val.wires target).scope
  | @snoc steps step priorAtlas currentWireImage currentDying currentScope
      trace priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact receipt applicationLanding
      induction =>
      let splitTarget : Fin
          (step.prior.val.wireCount +
            step.attachment.fragmentInternalWires.length) :=
        Fin.cast step.checked_wireCount target
      have targetExact :
          target = Fin.cast step.checked_wireCount.symm splitTarget := by
        apply Fin.ext
        rfl
      rw [targetExact]
      refine Fin.addCases (motive := fun splitTarget =>
        (extendAtlas step priorAtlas receipt applicationLanding).rows.regionAt
            (step.checked.val.wires
              (Fin.cast step.checked_wireCount.symm splitTarget)).scope =
          boundWireOriginScope
            ((RelationJoinConstructionTrace.snoc step trace
              priorWireImageExact priorDyingExact priorScopeExact
              relationArgsExact sourceParametersExact receipt
              applicationLanding).boundWireOrigin
                (Fin.cast step.checked_wireCount.symm splitTarget))) ?_ ?_
          splitTarget
      · intro priorTarget
        have checkedTarget :
            Fin.cast step.checked_wireCount.symm
                (Fin.castAdd step.attachment.fragmentInternalWires.length
                  priorTarget) =
              step.checkedPriorWire priorTarget := by
          apply Fin.ext
          rfl
        rw [checkedTarget, step.checkedPriorWire_scope]
        change
          (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).regionAt
              (step.checkedPriorRegion
                (step.prior.val.wires priorTarget).scope) = _
        rw [← receipt.retainedRegionAllocation,
          extendRows_regionAt_prior, induction priorTarget]
        rw [trace.boundWireOrigin_checkedPrior step priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact
          sourceParametersExact receipt applicationLanding priorTarget]
        exact (boundWireOriginScope_lift step
          (trace.boundWireOrigin priorTarget)).symm
      · intro fresh
        have baseCount :
            step.base.val.wireCount = step.prior.val.wireCount := by
          rw [step.baseGenerated]
          simp [ConcreteDiagram.DenseErasure.eraseNodeCandidate,
            Internal.retainedWires, ConcreteDiagram.wiresList,
            Data.Finite.allFin_eq_finRange]
        have checkedTarget :
            Fin.cast step.checked_wireCount.symm
                (Fin.natAdd step.prior.val.wireCount fresh) =
              Internal.checkedWire step.generated
                (step.attachment.freshWire fresh) := by
          apply Fin.ext
          simp [Internal.checkedWire, ConcreteSpliceAttachment.freshWire,
            baseCount]
        rw [checkedTarget, Internal.checkedWire_scope_transport,
          ConcreteSpliceAttachment.diagram_wire_freshWire_scope]
        have scopeTarget :
            Internal.checkedRegion step.generated
                (step.attachment.fragmentRegion
                  (content.val.diagram.wires
                    (step.attachment.fragmentInternalWires.get fresh)).scope) =
              step.checkedFragmentRegion
                (content.val.diagram.wires
                  (step.attachment.fragmentInternalWires.get fresh)).scope := by
          apply Fin.ext
          rfl
        rw [scopeTarget]
        rw [extendAtlas_regionAt_checkedFragmentRegion]
        rw [trace.boundWireOrigin_fresh step priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact
          sourceParametersExact receipt applicationLanding fresh]
        simp [boundWireOriginScope]

/-- Every transported source wire retains its dense position throughout the
raw construction trace. -/
@[simp] theorem RelationJoinConstructionTrace.finalWireImage_val
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying finalScope)
    (sourceWire : source.val.WireId) :
    (finalWireImage sourceWire).val = sourceWire.val := by
  induction trace with
  | nil => rfl
  | @snoc steps step priorAtlas currentWireImage currentDying currentScope
      trace priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact receipt applicationLanding
      induction =>
      rw [step.checkedWireImage_eq_checkedPriorWire,
        step.checkedPriorWire_val]
      have imageExact : step.priorWireImage = currentWireImage :=
        eq_of_heq priorWireImageExact
      rw [imageExact]
      exact induction

/-- The bound raw wire carrying one terminal wire origin, before deleting the
exhausted relation wire. -/
def RelationJoinResult.boundWireOfFinalOrigin
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters) :
    FinalWireOrigin result → result.boundFinal.val.WireId
  | .inl wire => result.boundWireImage wire.1
  | .inr origin =>
      Fin.cast result.construction_trace.boundWireCount_exact.symm
        (Fin.natAdd source.val.wireCount
          (locateConstructionWireOrigin origin).1)

/-- The selected bound wire has exactly the requested construction origin. -/
theorem RelationJoinResult.boundWireOfFinalOrigin_origin
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    result.construction_trace.boundWireOrigin
        (result.boundWireOfFinalOrigin origin) =
      match origin with
      | .inl wire => .inl wire.1
      | .inr internal => .inr internal := by
  cases origin with
  | inl wire =>
      unfold RelationJoinResult.boundWireOfFinalOrigin
      unfold RelationJoinConstructionTrace.boundWireOrigin
      have targetExact :
          Fin.cast result.construction_trace.boundWireCount_exact
              (result.boundWireImage wire.1) =
            Fin.castAdd (constructionWireOriginRows result.steps).length
              wire.1 := by
        apply Fin.ext
        exact result.construction_trace.finalWireImage_val wire.1
      rw [targetExact, Fin.addCases_left]
  | inr internal =>
      unfold RelationJoinResult.boundWireOfFinalOrigin
      unfold RelationJoinConstructionTrace.boundWireOrigin
      let landing := locateConstructionWireOrigin internal
      have targetExact :
          Fin.cast result.construction_trace.boundWireCount_exact
              (Fin.cast
                result.construction_trace.boundWireCount_exact.symm
                (Fin.natAdd source.val.wireCount landing.1)) =
            Fin.natAdd source.val.wireCount landing.1 := by
        apply Fin.ext
        rfl
      rw [targetExact, Fin.addCases_right]
      exact congrArg Sum.inr landing.2.exact

/-- The bound raw wire selected by a terminal origin is never the exhausted
relation wire. -/
theorem RelationJoinResult.boundWireOfFinalOrigin_survives
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    result.boundWireOfFinalOrigin origin ≠ result.boundDying := by
  cases origin with
  | inl wire =>
      intro same
      exact wire.2 (result.boundWireImage_injective same)
  | inr internal =>
      intro same
      have values := congrArg Fin.val same
      have internalValue :
          (result.boundWireOfFinalOrigin (.inr internal)).val =
            source.val.wireCount +
              (locateConstructionWireOrigin internal).1.val := by
        rfl
      have dyingValue : result.boundDying.val = dying.val :=
        result.construction_trace.finalWireImage_val dying
      rw [internalValue, dyingValue] at values
      omega

theorem survivingSourceWirePosition_val
    (wire : { wire : source.val.WireId // wire ≠ dying }) :
    (survivingSourceWirePosition (dying := dying) wire).val =
      if wire.1.val < dying.val then wire.1.val else wire.1.val - 1 := by
  unfold survivingSourceWirePosition
  change (dropFin
    (Fin.cast (sourceSurvivingWireCount_add_one dying).symm dying)
    (Fin.cast (sourceSurvivingWireCount_add_one dying).symm wire.1) _).val = _
  unfold dropFin
  split <;> rename_i before
  · have direct : wire.1.val < dying.val := by simpa using before
    simp [direct]
  · have direct : ¬ wire.1.val < dying.val := by simpa using before
    simp [direct]

theorem locateFinalWireOrigin_val_source
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (wire : { wire : source.val.WireId // wire ≠ dying }) :
    (locateFinalWireOrigin result (.inl wire)).1.val =
      (survivingSourceWirePosition (dying := dying) wire).val := by
  rfl

theorem locateFinalWireOrigin_val_internal
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (internal : ConstructionWireOrigin result.steps) :
    (locateFinalWireOrigin result (.inr internal)).1.val =
      (source.val.wireCount - 1) +
        (locateConstructionWireOrigin internal).1.val := by
  simp [locateFinalWireOrigin, Data.Finite.allFin_eq_finRange]

/-- Deleting the exhausted wire sends the bound representative of an origin
to the inverse terminal wire-origin position. -/
theorem RelationJoinResult.plainBoundWireImage_boundWireOfFinalOrigin
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    result.plainBoundWireImage
        (result.boundWireOfFinalOrigin origin)
        (result.boundWireOfFinalOrigin_survives origin) =
      (finalWireOriginEquiv result).invFun origin := by
  apply Fin.ext
  rw [result.plainBoundWireImage_val_dropFin]
  cases origin with
  | inl wire =>
      have boundValue :
          (result.boundWireOfFinalOrigin (.inl wire)).val = wire.1.val :=
        result.construction_trace.finalWireImage_val wire.1
      have dyingValue : result.boundDying.val = dying.val :=
        result.construction_trace.finalWireImage_val dying
      rw [show ((finalWireOriginEquiv result).invFun (.inl wire)).val =
          (locateFinalWireOrigin result (.inl wire)).1.val by rfl,
        locateFinalWireOrigin_val_source]
      unfold dropFin
      simp only [Fin.val_cast]
      rw [survivingSourceWirePosition_val]
      split <;> rename_i before
      · simp only [Fin.val_mk]
        split <;> rename_i sourceBefore <;> omega
      · simp only [Fin.val_mk]
        split <;> rename_i sourceBefore <;> omega
  | inr internal =>
      have boundValue :
          (result.boundWireOfFinalOrigin (.inr internal)).val =
            source.val.wireCount +
              (locateConstructionWireOrigin internal).1.val := by
        rfl
      have dyingValue : result.boundDying.val = dying.val :=
        result.construction_trace.finalWireImage_val dying
      rw [show ((finalWireOriginEquiv result).invFun (.inr internal)).val =
          (locateFinalWireOrigin result (.inr internal)).1.val by rfl,
        locateFinalWireOrigin_val_internal]
      unfold dropFin
      simp only [Fin.val_cast]
      have sourcePositive : 0 < source.val.wireCount :=
        Nat.zero_lt_of_lt dying.isLt
      split <;> rename_i before
      · simp only [Fin.val_mk]
        omega
      · simp only [Fin.val_mk]
        omega

/-- The actual terminal raw wire at an origin carries exactly that origin's
intrinsic signature. -/
theorem RelationJoinResult.plainFinal_wire_signature_at_origin
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    (result.plainFinal.val.wires
      ((finalWireOriginEquiv result).invFun origin)).sig =
        expectedFinalWireSignature result origin := by
  rw [← result.plainBoundWireImage_boundWireOfFinalOrigin origin]
  rw [result.plainBoundWireImage_signature]
  rw [result.construction_trace.boundWire_signature_exact]
  rw [result.boundWireOfFinalOrigin_origin]
  cases origin <;> rfl

theorem RelationJoinResult.finalRegionOriginEquiv_plainBoundRegionImage
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (region : result.boundFinal.val.RegionId) :
    result.finalRegionOriginEquiv (result.plainBoundRegionImage region) =
      result.constructionAtlas.rows.regionAt region := by
  change result.constructionAtlas.rows.regionAt
      (Fin.cast result.plainFinal_regionCount
        (result.plainBoundRegionImage region)) = _
  congr 1
  apply Fin.ext
  exact result.plainBoundRegionImage_val region

/-- The actual terminal raw wire at an origin is scoped by exactly that
origin's construction-owned region. -/
theorem RelationJoinResult.plainFinal_wire_scope_at_origin
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    result.finalRegionOriginEquiv
        (result.plainFinal.val.wires
          ((finalWireOriginEquiv result).invFun origin)).scope =
      expectedFinalWireScope result origin := by
  rw [← result.plainBoundWireImage_boundWireOfFinalOrigin origin]
  rw [result.plainBoundWireImage_scope]
  rw [result.finalRegionOriginEquiv_plainBoundRegionImage]
  rw [result.construction_trace.boundWire_scope_exact]
  rw [result.boundWireOfFinalOrigin_origin]
  cases origin <;> rfl

end ConcreteWireQuantifier

end VisualProof
