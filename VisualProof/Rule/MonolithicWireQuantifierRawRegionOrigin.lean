import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawOriginFacts

namespace VisualProof

namespace MonolithicWireQuantifier

open ConcreteWireQuantifier

section RawRegionOrigin

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}

/-- The single neutral region-origin authority for every construction prefix. -/
abbrev RelationJoinPrefixRegionOrigin
    (steps : List (RelationJoinStep source dying content)) :=
  source.val.RegionId ⊕
    Σ _occurrence : Fin steps.length,
      { region : content.val.diagram.RegionId //
        region ≠ content.val.diagram.root }

/-- Allocation-neutral node origins for a construction prefix.  Source nodes
remain in this broad carrier while the landing relation records whether a
later splice consumes them. -/
abbrev RelationJoinPrefixNodeOrigin
    (steps : List (RelationJoinStep source dying content)) :=
  source.val.NodeId ⊕
    Σ occurrence : Fin steps.length,
      content.val.diagram.NodeId ⊕
        Fin ((steps.get occurrence).attachment.identityRequests.length)

/-- A broad prefix node origin is live exactly when it has not been consumed
as a source application.  Fresh occurrence nodes are never consumed by this
source-indexed construction trace. -/
def RelationJoinPrefixNodeLive
    {steps : List (RelationJoinStep source dying content)} :
    RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps → Prop
  | .inl node => node ∉ steps.map RelationJoinStep.application
  | .inr _ => True

namespace ConcreteWireQuantifier.RelationJoinConstructionTrace

/-- Lift a broad node origin across one checked construction snoc. -/
def prefixNodeOriginLift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps →
    RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])
  | .inl node => .inl node
  | .inr ⟨occurrence, .inl node⟩ =>
      .inr ⟨Fin.cast (by simp) (Fin.castAdd 1 occurrence), .inl node⟩
  | .inr ⟨occurrence, .inr request⟩ =>
      .inr ⟨Fin.cast (by simp) (Fin.castAdd 1 occurrence),
        .inr (Fin.cast (by
          change (steps[occurrence.val]).attachment.identityRequests.length =
            ((steps ++ [step])[occurrence.val]).attachment.identityRequests.length
          rw [List.getElem_append_left occurrence.isLt]) request)⟩

/-- Copied content-node origin introduced by the newest occurrence. -/
def prefixNodeFreshContentOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId) :
    RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step]) :=
  .inr ⟨Fin.cast (by simp) (Fin.last steps.length), .inl node⟩

/-- Attachment-request node origin introduced by the newest occurrence. -/
def prefixNodeFreshRequestOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length) :
    RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step]) :=
  .inr ⟨Fin.cast (by simp) (Fin.last steps.length),
    .inr (Fin.cast (by
      change step.attachment.identityRequests.length =
        ((steps ++ [step])[steps.length]).attachment.identityRequests.length
      exact congrArg
        (fun current : RelationJoinStep source dying content =>
          current.attachment.identityRequests.length)
        (List.getElem_concat_length rfl _).symm) request)⟩

/-- The computational snoc decomposition of one broad node origin. -/
abbrev PrefixNodeOriginView
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])) : Type :=
  (Σ priorOrigin : RelationJoinPrefixNodeOrigin (source := source)
      (dying := dying) (content := content) steps,
    PLift (origin = prefixNodeOriginLift step priorOrigin)) ⊕
  ((Σ node : content.val.diagram.NodeId,
      PLift (origin = prefixNodeFreshContentOrigin step node)) ⊕
    (Σ request : Fin step.attachment.identityRequests.length,
      PLift (origin = prefixNodeFreshRequestOrigin step request)))

/-- Compute the unique snoc case of a broad node origin without searching an
origin table. -/
def prefixNodeOriginView
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step])) :
    PrefixNodeOriginView step origin := by
  classical
  cases origin with
  | inl node =>
      exact .inl ⟨.inl node, ⟨rfl⟩⟩
  | inr occurrence =>
      rcases occurrence with ⟨index, inner⟩
      by_cases last : index.val = steps.length
      · have indexExact :
            index = Fin.cast (by simp) (Fin.last steps.length) := by
          apply Fin.ext
          simpa using last
        subst index
        cases inner with
        | inl node =>
            exact .inr (.inl ⟨node, ⟨by
              simp [prefixNodeFreshContentOrigin]⟩⟩)
        | inr request =>
            let request' : Fin step.attachment.identityRequests.length :=
              Fin.cast (by
                change
                  ((steps ++ [step])[steps.length]).attachment.identityRequests.length =
                    step.attachment.identityRequests.length
                rw [List.getElem_concat_length]
                rfl) request
            exact .inr (.inr ⟨request', ⟨by
              simp [prefixNodeFreshRequestOrigin, request']⟩⟩)
      · have priorBound : index.val < steps.length := by
          have bound := index.isLt
          simp at bound
          omega
        let priorIndex : Fin steps.length := ⟨index.val, priorBound⟩
        cases inner with
        | inl node =>
            exact .inl ⟨.inr ⟨priorIndex, .inl node⟩, ⟨by
              apply congrArg Sum.inr
              apply Sigma.ext
              · apply Fin.ext
                rfl
              · rfl⟩⟩
        | inr request =>
            let request' :
                Fin ((steps.get priorIndex).attachment.identityRequests.length) :=
              Fin.cast (by
                apply congrArg (fun current :
                  RelationJoinStep source dying content =>
                    current.attachment.identityRequests.length)
                simp only [List.get_eq_getElem]
                rw [List.getElem_append_left priorBound]) request
            exact .inl ⟨.inr ⟨priorIndex, .inr request'⟩, ⟨by
              simp [prefixNodeOriginLift, request', priorIndex]⟩⟩

/-- Liveness of a lifted origin implies liveness in the prior prefix. -/
theorem prefixNodeOriginLift_live
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (live : RelationJoinPrefixNodeLive
      (prefixNodeOriginLift step origin)) :
    RelationJoinPrefixNodeLive origin := by
  cases origin with
  | inl node =>
      intro member
      apply live
      simpa [RelationJoinPrefixNodeLive, prefixNodeOriginLift] using
        List.mem_append_left
          ([step].map RelationJoinStep.application) member
  | inr occurrence =>
      trivial

theorem prefixNodeOriginLift_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (prefixNodeOriginLift (steps := steps) step) := by
  intro left right same
  cases left with
  | inl leftNode =>
      cases right with
      | inl rightNode => simpa [prefixNodeOriginLift] using same
      | inr rightOccurrence =>
          rcases rightOccurrence with ⟨rightIndex, rightNode⟩
          cases rightNode <;> simp [prefixNodeOriginLift] at same
  | inr leftOccurrence =>
      cases right with
      | inl rightNode =>
          rcases leftOccurrence with ⟨leftIndex, leftNode⟩
          cases leftNode <;> simp [prefixNodeOriginLift] at same
      | inr rightOccurrence =>
          rcases leftOccurrence with ⟨leftIndex, leftNode⟩
          rcases rightOccurrence with ⟨rightIndex, rightNode⟩
          cases leftNode with
          | inl leftContent =>
              cases rightNode with
              | inl rightContent =>
                  simp only [prefixNodeOriginLift, Sum.inr.injEq,
                    Sigma.mk.injEq] at same
                  have indexSame : leftIndex = rightIndex := by
                    apply Fin.ext
                    simpa using congrArg Fin.val same.1
                  subst rightIndex
                  have contentSame : leftContent = rightContent := by
                    simpa using eq_of_heq same.2
                  subst rightContent
                  rfl
              | inr rightRequest =>
                  simp [prefixNodeOriginLift] at same
                  have indexSame : leftIndex = rightIndex := by
                    apply Fin.ext
                    simpa using congrArg Fin.val same.1
                  subst rightIndex
                  have impossible := eq_of_heq same.2
                  cases impossible
          | inr leftRequest =>
              cases rightNode with
              | inl rightContent =>
                  simp [prefixNodeOriginLift] at same
                  have indexSame : leftIndex = rightIndex := by
                    apply Fin.ext
                    simpa using congrArg Fin.val same.1
                  subst rightIndex
                  have impossible := eq_of_heq same.2
                  cases impossible
              | inr rightRequest =>
                  simp only [prefixNodeOriginLift, Sum.inr.injEq,
                    Sigma.mk.injEq] at same
                  have indexSame : leftIndex = rightIndex := by
                    apply Fin.ext
                    simpa using congrArg Fin.val same.1
                  subst rightIndex
                  have castSame := Sum.inr.inj (eq_of_heq same.2)
                  have requestSame : leftRequest = rightRequest := by
                    apply Fin.ext
                    simpa using congrArg Fin.val castSame
                  subst rightRequest
                  rfl

theorem prefixNodeOriginLift_ne_freshContent
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (node : content.val.diagram.NodeId) :
    prefixNodeOriginLift step origin ≠
      prefixNodeFreshContentOrigin step node := by
  intro same
  cases origin with
  | inl sourceNode => simp [prefixNodeOriginLift,
      prefixNodeFreshContentOrigin] at same
  | inr occurrence =>
      rcases occurrence with ⟨index, inner⟩
      cases inner <;>
        simp only [prefixNodeOriginLift] at same
      all_goals
        have bound := index.isLt
        have indexSame := congrArg (fun value => match value with
          | .inl _ => 0
          | .inr occurrence => occurrence.1.val + 1) same
        simp [prefixNodeFreshContentOrigin] at indexSame
        omega

theorem prefixNodeOriginLift_ne_freshRequest
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (request : Fin step.attachment.identityRequests.length) :
    prefixNodeOriginLift step origin ≠
      prefixNodeFreshRequestOrigin step request := by
  intro same
  cases origin with
  | inl sourceNode => simp [prefixNodeOriginLift,
      prefixNodeFreshRequestOrigin] at same
  | inr occurrence =>
      rcases occurrence with ⟨index, inner⟩
      cases inner <;>
        simp only [prefixNodeOriginLift] at same
      all_goals
        have bound := index.isLt
        have indexSame := congrArg (fun value => match value with
          | .inl _ => 0
          | .inr occurrence => occurrence.1.val + 1) same
        simp [prefixNodeFreshRequestOrigin] at indexSame
        omega

theorem prefixNodeFreshContent_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (prefixNodeFreshContentOrigin (steps := steps) step) := by
  intro left right same
  simpa [prefixNodeFreshContentOrigin] using same

theorem prefixNodeFreshRequest_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (prefixNodeFreshRequestOrigin (steps := steps) step) := by
  intro left right same
  simp only [prefixNodeFreshRequestOrigin, Sum.inr.injEq,
    Sigma.mk.injEq] at same
  have castSame := Sum.inr.inj (eq_of_heq same.2)
  apply Fin.ext
  simpa using congrArg Fin.val castSame

theorem prefixNodeFreshContent_ne_freshRequest
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId)
    (request : Fin step.attachment.identityRequests.length) :
    prefixNodeFreshContentOrigin (steps := steps) step node ≠
      prefixNodeFreshRequestOrigin (steps := steps) step request := by
  intro same
  have tagSame := congrArg (fun origin => match origin with
    | .inl _ => true
    | .inr occurrence => match occurrence.2 with
      | .inl _ => true
      | .inr _ => false) same
  simpa [prefixNodeFreshContentOrigin,
    prefixNodeFreshRequestOrigin] using tagSame

/-- Lift a prefix origin across one checked construction snoc. -/
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

/-- The new occurrence origin introduced by one checked construction snoc. -/
def prefixRegionFreshOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) (steps ++ [step]) :=
  .inr ⟨Fin.cast (by simp) (Fin.last steps.length), region⟩

theorem prefixRegionOriginLift_injective
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    Function.Injective (prefixRegionOriginLift (steps := steps) step) := by
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
          have regionSame : leftRegion = rightRegion :=
            congrArg Sigma.snd sigmaSame
          cases indexSame
          cases regionSame
          rfl

theorem prefixRegionOriginLift_ne_fresh
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) steps)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    prefixRegionOriginLift step origin ≠ prefixRegionFreshOrigin step region := by
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
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    {left right : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }}
    (same : prefixRegionFreshOrigin (steps := steps) step left =
      prefixRegionFreshOrigin (steps := steps) step right) :
    left = right := by
  have sigmaSame := Sum.inr.inj same
  exact congrArg Sigma.snd sigmaSame

theorem prefixRegionOrigin_cases
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) (steps ++ [step])) :
    (∃ prior, origin = prefixRegionOriginLift step prior) ∨
      ∃ region, origin = prefixRegionFreshOrigin step region := by
  cases origin with
  | inl region => exact Or.inl ⟨.inl region, rfl⟩
  | inr occurrence =>
      rcases occurrence with ⟨occurrence, region⟩
      let occurrence' : Fin (steps.length + 1) :=
        Fin.cast (by simp) occurrence
      refine Fin.lastCases
        (motive := fun index =>
          (∃ prior, Sum.inr ⟨Fin.cast (by simp) index, region⟩ =
            prefixRegionOriginLift step prior) ∨
          ∃ fresh, Sum.inr ⟨Fin.cast (by simp) index, region⟩ =
            prefixRegionFreshOrigin step fresh)
        ?_ ?_ occurrence'
      · exact Or.inr ⟨region, by
          apply congrArg Sum.inr
          apply Sigma.ext
          apply Fin.ext
          rfl
          exact HEq.rfl⟩
      · intro priorOccurrence
        exact Or.inl ⟨.inr ⟨priorOccurrence, region⟩, by
          apply congrArg Sum.inr
          apply Sigma.ext
          apply Fin.ext
          rfl
          exact HEq.rfl⟩

end ConcreteWireQuantifier.RelationJoinConstructionTrace

end RawRegionOrigin

end MonolithicWireQuantifier

end VisualProof
