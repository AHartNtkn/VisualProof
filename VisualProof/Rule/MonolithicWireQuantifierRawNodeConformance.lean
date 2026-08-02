import VisualProof.Rule.MonolithicWireQuantifierRawRegionConformance

namespace VisualProof

namespace MonolithicWireQuantifier

open _root_.VisualProof.ConcreteWireQuantifier

section RawNodeConformance

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

namespace RelationJoinRawOriginAtlas

open ConcreteWireQuantifier.RelationJoinConstructionTrace

/-- Canonical node payload for one broad construction-prefix origin. -/
def expectedPrefixNodeData
    (steps : List (RelationJoinStep source dying content)) :
    RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps →
      RelationJoinRawNodeData
        (RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
          (content := content) steps) definitions.length
  | .inl node =>
      match source.val.nodes node with
      | .atom region args => .atom (.inl region) args
      | .ref region definition args => .ref (.inl region) definition args
      | .identity region sig arity => .identity (.inl region) sig arity
  | .inr ⟨occurrence, .inl node⟩ =>
      match content.val.diagram.nodes node with
      | .atom region args =>
          .atom (prefixContentRegionOrigin steps occurrence region) args
      | .ref region definition args =>
          .ref (prefixContentRegionOrigin steps occurrence region)
            definition args
      | .identity region sig arity =>
          .identity (prefixContentRegionOrigin steps occurrence region)
            sig arity
  | .inr ⟨occurrence, .inr request⟩ =>
      let step := steps.get occurrence
      let requestData := step.attachment.identityRequests.get request
      .identity (.inl step.sourceRegion) requestData.sig
        requestData.attachments.length

/-- Lift only the neutral region carrier of one prefix node payload. -/
def liftPrefixNodeData
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    RelationJoinRawNodeData
        (RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
          (content := content) steps) definitions.length →
      RelationJoinRawNodeData
        (RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
          (content := content) (steps ++ [step])) definitions.length
  | .atom region args => .atom (prefixRegionOriginLift step region) args
  | .ref region definition args =>
      .ref (prefixRegionOriginLift step region) definition args
  | .identity region sig arity =>
      .identity (prefixRegionOriginLift step region) sig arity

theorem prefixContentRegionOrigin_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (occurrence : Fin steps.length)
    (region : content.val.diagram.RegionId) :
    prefixContentRegionOrigin (steps ++ [step])
        (Fin.cast (by simp) (Fin.castAdd 1 occurrence)) region =
      prefixRegionOriginLift step
        (prefixContentRegionOrigin steps occurrence region) := by
  by_cases root : region = content.val.diagram.root <;>
    simp [prefixContentRegionOrigin, root, prefixRegionOriginLift]

@[simp] theorem steps_get_liftedOccurrence
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (occurrence : Fin steps.length) :
    (steps ++ [step]).get
        (Fin.cast (by simp) (Fin.castAdd 1 occurrence)) =
      steps.get occurrence := by
  simp only [List.get_eq_getElem]
  change (steps ++ [step])[occurrence.val] = steps[occurrence.val]
  exact List.getElem_append_left occurrence.isLt

@[simp] theorem steps_get_freshOccurrence
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    (steps ++ [step]).get (Fin.cast (by simp) (Fin.last steps.length)) =
      step := by
  simp only [List.get_eq_getElem]
  change (steps ++ [step])[steps.length] = step
  exact List.getElem_concat_length rfl _

theorem identityRequest_sig_of_step_eq
    {left right : RelationJoinStep source dying content}
    (same : left = right)
    (request : Fin right.attachment.identityRequests.length) :
    (left.attachment.identityRequests.get
        (Fin.cast (congrArg
          (fun current : RelationJoinStep source dying content =>
            current.attachment.identityRequests.length) same).symm request)).sig =
      (right.attachment.identityRequests.get request).sig := by
  subst right
  rfl

theorem identityRequest_arity_of_step_eq
    {left right : RelationJoinStep source dying content}
    (same : left = right)
    (request : Fin right.attachment.identityRequests.length) :
    (left.attachment.identityRequests.get
        (Fin.cast (congrArg
          (fun current : RelationJoinStep source dying content =>
            current.attachment.identityRequests.length) same).symm request)).attachments.length =
      (right.attachment.identityRequests.get request).attachments.length := by
  subst right
  rfl

theorem expectedPrefixNodeData_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : RelationJoinPrefixNodeOrigin (source := source)
      (dying := dying) (content := content) steps) :
    expectedPrefixNodeData (steps ++ [step])
        (prefixNodeOriginLift step origin) =
      liftPrefixNodeData step (expectedPrefixNodeData steps origin) := by
  cases origin with
  | inl node =>
      cases data : source.val.nodes node <;>
        simp [expectedPrefixNodeData, liftPrefixNodeData, data,
          prefixNodeOriginLift, prefixRegionOriginLift]
  | inr occurrence =>
      rcases occurrence with ⟨occurrence, node⟩
      cases node with
      | inl node =>
          cases data : content.val.diagram.nodes node <;>
            simp [expectedPrefixNodeData, liftPrefixNodeData, data,
              prefixNodeOriginLift, prefixContentRegionOrigin_lift]
      | inr request =>
          have stepExact : (steps ++ [step])[occurrence.val] =
              steps[occurrence.val] :=
            List.getElem_append_left occurrence.isLt
          simp [expectedPrefixNodeData, liftPrefixNodeData,
            prefixNodeOriginLift, prefixRegionOriginLift, stepExact]
          exact ⟨by simpa using
              identityRequest_sig_of_step_eq stepExact request,
            by simpa using
              identityRequest_arity_of_step_eq stepExact request⟩

theorem expectedPrefixNodeData_freshContent
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId) :
    expectedPrefixNodeData (steps ++ [step])
        (prefixNodeFreshContentOrigin step node) =
      match content.val.diagram.nodes node with
      | .atom region args =>
          .atom (if root : region = content.val.diagram.root then
            .inl step.sourceRegion
          else prefixRegionFreshOrigin step ⟨region, root⟩) args
      | .ref region definition args =>
          .ref (if root : region = content.val.diagram.root then
            .inl step.sourceRegion
          else prefixRegionFreshOrigin step ⟨region, root⟩)
            definition args
      | .identity region sig arity =>
          .identity (if root : region = content.val.diagram.root then
            .inl step.sourceRegion
          else prefixRegionFreshOrigin step ⟨region, root⟩) sig arity := by
  cases data : content.val.diagram.nodes node <;>
    simp [expectedPrefixNodeData, prefixNodeFreshContentOrigin,
      prefixContentRegionOrigin, prefixRegionFreshOrigin, data]

theorem expectedPrefixNodeData_freshRequest
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length) :
    expectedPrefixNodeData (steps ++ [step])
        (prefixNodeFreshRequestOrigin step request) =
      let requestData := step.attachment.identityRequests.get request
      .identity (.inl step.sourceRegion) requestData.sig
        requestData.attachments.length := by
  have stepExact : (steps ++ [step])[steps.length] = step :=
    List.getElem_concat_length rfl _
  simp [expectedPrefixNodeData, prefixNodeFreshRequestOrigin, stepExact]
  exact ⟨by simpa using identityRequest_sig_of_step_eq stepExact request,
    by simpa using identityRequest_arity_of_step_eq stepExact request⟩

theorem expectedPrefixNodeData_result
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawNodeOrigin result) :
    expectedPrefixNodeData result.steps origin.1 =
      expectedNodeData result origin := by
  rcases origin with ⟨origin, live⟩
  cases origin with
  | inl node =>
      cases data : source.val.nodes node <;>
        simp [expectedPrefixNodeData, expectedNodeData, data]
  | inr occurrence =>
      rcases occurrence with ⟨occurrence, node⟩
      cases node with
      | inl node =>
          cases data : content.val.diagram.nodes node <;>
            simp [expectedPrefixNodeData, expectedNodeData,
              prefixContentRegionOrigin, contentRegionOrigin, data]
      | inr request =>
          simp [expectedPrefixNodeData, expectedNodeData]

/-- The neutral region carrier named by an allocation-neutral node row. -/
def RelationJoinRawNodeData.regionOrigin
    {Region : Type} {definitionCount : Nat} :
    RelationJoinRawNodeData Region definitionCount → Region
  | .atom region _ => region
  | .ref region _ _ => region
  | .identity region _ _ => region

/-- Materialize an allocation-neutral node row at one concrete region. -/
def RelationJoinRawNodeData.materialize
    {Region : Type} {definitionCount regionCount : Nat}
    (data : RelationJoinRawNodeData Region definitionCount)
    (region : Fin regionCount) : CNode regionCount definitionCount :=
  match data with
  | .atom _ args => .atom region args
  | .ref _ definition args => .ref region definition args
  | .identity _ sig arity => .identity region sig arity

end RelationJoinRawOriginAtlas

namespace ConcreteWireQuantifier.RelationJoinConstructionTrace

open RelationJoinRawOriginAtlas

/-- A live lifted prefix row cannot be the application consumed by the next
construction step. -/
theorem prefixNodeLands_ne_application
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
    (priorNodeImageExact : HEq step.priorNodeImage currentNodeImage)
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (live : RelationJoinPrefixNodeLive (prefixNodeOriginLift step origin))
    (target : current.val.NodeId)
    (landing : PrefixNodeLands trace origin target) :
    priorNodeCast step priorExact target ≠ step.priorApplication := by
  subst current
  cases eq_of_heq priorNodeImageExact
  change target ≠ step.priorApplication
  intro targetExact
  subst target
  have sourceExact := relationJoinConstructionNodeOrigins_source trace
    step.application step.priorApplication step.priorApplicationImage
  have originExact : origin = (.inl step.application :
      RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
        (content := content) steps) :=
    landing.exact.symm.trans sourceExact
  subst origin
  simpa [RelationJoinPrefixNodeLive, prefixNodeOriginLift] using live

/-- One landed checked prefix node has its exact construction-derived row and
the construction-derived landing of its neutral region carrier. -/
structure PrefixNodeRowExact
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
    (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (target : final.val.NodeId) : Type where
  nodeLanding : PrefixNodeLands trace origin target
  regionTarget : final.val.RegionId
  regionLanding : PrefixRegionLands trace
    (expectedPrefixNodeData steps origin).regionOrigin regionTarget
  dataExact : final.val.nodes target =
    (expectedPrefixNodeData steps origin).materialize regionTarget

/-- Every landed prefix node carries exactly the construction-derived node
row, and its neutral region carrier lands through the region trace. -/
def prefixNodeLands_row_exact {args : List Sig} :
    ∀ {steps : List (RelationJoinStep source dying content)}
      {final : CheckedDiagram definitions}
      {finalRegionImage : source.val.RegionId → final.val.RegionId}
      {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
      {finalWireImage : source.val.WireId → final.val.WireId}
      {finalDying : final.val.WireId} {finalScope : final.val.RegionId},
      (trace : RelationJoinConstructionTrace source dying content parameters args
        steps final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope) →
      (origin : RelationJoinPrefixNodeOrigin (source := source) (dying := dying)
        (content := content) steps) →
      (target : final.val.NodeId) →
      PrefixNodeLands trace origin target →
      PrefixNodeRowExact trace origin target
  | _, _, _, _, _, _, _, .nil, origin, target, landing => by
      cases origin with
      | inl node =>
          have sourceLanding : PrefixNodeLands
              (source := source) (dying := dying) (content := content)
              (parameters := parameters) (args := args)
              (.nil) (.inl node) node :=
            ⟨relationJoinConstructionNodeOrigins_source
              (source := source) (dying := dying) (content := content)
              (parameters := parameters) (args := args)
              .nil node node rfl⟩
          have targetExact := prefixNodeLands_functional landing sourceLanding
          subst target
          cases data : source.val.nodes node with
          | atom region nodeArgs =>
              exact ⟨sourceLanding, region,
                by simpa [expectedPrefixNodeData, data,
                    RelationJoinRawNodeData.regionOrigin] using
                  (prefixRegionLands_source
                    (source := source) (dying := dying) (content := content)
                    (parameters := parameters) (args := args) .nil region), by
                  simp [expectedPrefixNodeData, data,
                    RelationJoinRawNodeData.regionOrigin,
                    RelationJoinRawNodeData.materialize]⟩
          | ref region definition nodeArgs =>
              exact ⟨sourceLanding, region,
                by simpa [expectedPrefixNodeData, data,
                    RelationJoinRawNodeData.regionOrigin] using
                  (prefixRegionLands_source
                    (source := source) (dying := dying) (content := content)
                    (parameters := parameters) (args := args) .nil region), by
                  simp [expectedPrefixNodeData, data,
                    RelationJoinRawNodeData.regionOrigin,
                    RelationJoinRawNodeData.materialize]⟩
          | identity region sig arity =>
              exact ⟨sourceLanding, region,
                by simpa [expectedPrefixNodeData, data,
                    RelationJoinRawNodeData.regionOrigin] using
                  (prefixRegionLands_source
                    (source := source) (dying := dying) (content := content)
                    (parameters := parameters) (args := args) .nil region), by
                  simp [expectedPrefixNodeData, data,
                    RelationJoinRawNodeData.regionOrigin,
                    RelationJoinRawNodeData.materialize]⟩
      | inr occurrence => exact Fin.elim0 occurrence.1
  | _, _, _, _, _, _, _,
      .snoc (steps := priorSteps) trace step priorExact
        priorRegionImageExact priorNodeImageExact priorWireImageExact
        priorDyingExact priorScopeExact relationArgsExact
        sourceParametersExact,
      origin, target, landing => by
      let recurse := prefixNodeLands_row_exact trace
      subst priorExact
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases Subsingleton.elim priorRegionImageExact HEq.rfl
      cases Subsingleton.elim priorNodeImageExact HEq.rfl
      cases Subsingleton.elim priorWireImageExact HEq.rfl
      cases Subsingleton.elim priorDyingExact HEq.rfl
      cases Subsingleton.elim priorScopeExact HEq.rfl
      have live : RelationJoinPrefixNodeLive origin :=
        relationJoinConstructionNodeOrigins_live _ origin
          (landing.exact ▸ List.get_mem _ _)
      rcases prefixNodeOriginView step origin with lifted | fresh
      · rcases lifted with ⟨priorOrigin, ⟨originExact⟩⟩
        subst origin
        have priorLive := prefixNodeOriginLift_live step priorOrigin live
        obtain ⟨priorTarget, priorLanding⟩ :=
          prefixNodeLands_total trace priorOrigin priorLive
        have different := prefixNodeLands_ne_application trace step rfl HEq.rfl
          priorOrigin live priorTarget priorLanding
        have castTarget : priorNodeCast step rfl priorTarget = priorTarget := by
          apply Fin.ext
          rfl
        have differentTarget : priorTarget ≠ step.priorApplication := by
          simpa [castTarget] using different
        let currentTarget := step.checkedPriorNode priorTarget differentTarget
        have currentLanding : PrefixNodeLands
            (.snoc trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
              rfl sourceParametersExact)
            (prefixNodeOriginLift step priorOrigin) currentTarget := by
          refine ⟨?_⟩
          have retainedExact :=
            relationJoinConstructionNodeOrigins_get_checkedPriorNode
              trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl
                sourceParametersExact priorTarget different
          simpa [currentTarget, castTarget] using retainedExact.trans
              (congrArg (prefixNodeOriginLift step) priorLanding.exact)
        have targetExact := prefixNodeLands_functional landing currentLanding
        subst target
        have priorRow := recurse priorOrigin priorTarget priorLanding
        refine ⟨currentLanding,
          step.checkedPriorRegion priorRow.regionTarget,
          ?_, ?_⟩
        · rw [expectedPrefixNodeData_lift]
          cases expected : expectedPrefixNodeData _ priorOrigin <;>
            simp only [liftPrefixNodeData,
              RelationJoinRawNodeData.regionOrigin] <;>
            exact Or.inl ⟨_, _, priorRow.regionLanding, rfl, rfl⟩
        rw [expectedPrefixNodeData_lift, step.checkedPriorNode_data,
          priorRow.dataExact]
        cases expectedPrefixNodeData _ priorOrigin <;>
          simp [RelationJoinRawNodeData.materialize, liftPrefixNodeData,
            RelationJoinRawNodeData.regionOrigin, CNode.relocate,
            CNode.region]
      · rcases fresh with contentOrigin | requestOrigin
        · rcases contentOrigin with ⟨node, ⟨originExact⟩⟩
          subst origin
          have currentLanding : PrefixNodeLands
              (.snoc trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
                rfl sourceParametersExact)
              (prefixNodeFreshContentOrigin step node)
              (step.checkedFragmentNode node) := by
            exact ⟨relationJoinConstructionNodeOrigins_get_checkedFragmentNode
              trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl
                sourceParametersExact node⟩
          have targetExact := prefixNodeLands_functional landing currentLanding
          subst target
          cases data : content.val.diagram.nodes node with
          | atom region nodeArgs =>
              by_cases root : region = content.val.diagram.root
              · refine ⟨currentLanding, step.checkedFragmentRegion region,
                  ?_, ?_⟩
                rw [expectedPrefixNodeData_freshContent]
                simp only [data, root, dif_pos,
                  RelationJoinRawNodeData.regionOrigin]
                rw [step.checkedFragmentRegion_root_eq_checkedRegionImage]
                exact prefixRegionLands_source _ step.sourceRegion
                rw [step.checkedFragmentNode_data, data]
                simp [expectedPrefixNodeData_freshContent, data, root,
                  RelationJoinRawNodeData.regionOrigin,
                  RelationJoinRawNodeData.materialize, CNode.relocate,
                  CNode.region]
              · refine ⟨currentLanding, step.checkedFragmentRegion region,
                  ?_, ?_⟩
                rw [expectedPrefixNodeData_freshContent]
                simp only [data, root, dif_neg,
                  RelationJoinRawNodeData.regionOrigin]
                exact Or.inr ⟨⟨region, root⟩, rfl, rfl⟩
                rw [step.checkedFragmentNode_data, data]
                simp [expectedPrefixNodeData_freshContent, data, root,
                  RelationJoinRawNodeData.regionOrigin,
                  RelationJoinRawNodeData.materialize, CNode.relocate,
                  CNode.region]
          | ref region definition nodeArgs =>
              by_cases root : region = content.val.diagram.root
              · refine ⟨currentLanding, step.checkedFragmentRegion region,
                  ?_, ?_⟩
                rw [expectedPrefixNodeData_freshContent]
                simp only [data, root, dif_pos,
                  RelationJoinRawNodeData.regionOrigin]
                rw [step.checkedFragmentRegion_root_eq_checkedRegionImage]
                exact prefixRegionLands_source _ step.sourceRegion
                rw [step.checkedFragmentNode_data, data]
                simp [expectedPrefixNodeData_freshContent, data, root,
                  RelationJoinRawNodeData.regionOrigin,
                  RelationJoinRawNodeData.materialize, CNode.relocate,
                  CNode.region]
              · refine ⟨currentLanding, step.checkedFragmentRegion region,
                  ?_, ?_⟩
                rw [expectedPrefixNodeData_freshContent]
                simp only [data, root, dif_neg,
                  RelationJoinRawNodeData.regionOrigin]
                exact Or.inr ⟨⟨region, root⟩, rfl, rfl⟩
                rw [step.checkedFragmentNode_data, data]
                simp [expectedPrefixNodeData_freshContent, data, root,
                  RelationJoinRawNodeData.regionOrigin,
                  RelationJoinRawNodeData.materialize, CNode.relocate,
                  CNode.region]
          | identity region sig arity =>
              by_cases root : region = content.val.diagram.root
              · refine ⟨currentLanding, step.checkedFragmentRegion region,
                  ?_, ?_⟩
                rw [expectedPrefixNodeData_freshContent]
                simp only [data, root, dif_pos,
                  RelationJoinRawNodeData.regionOrigin]
                rw [step.checkedFragmentRegion_root_eq_checkedRegionImage]
                exact prefixRegionLands_source _ step.sourceRegion
                rw [step.checkedFragmentNode_data, data]
                simp [expectedPrefixNodeData_freshContent, data, root,
                  RelationJoinRawNodeData.regionOrigin,
                  RelationJoinRawNodeData.materialize, CNode.relocate,
                  CNode.region]
              · refine ⟨currentLanding, step.checkedFragmentRegion region,
                  ?_, ?_⟩
                rw [expectedPrefixNodeData_freshContent]
                simp only [data, root, dif_neg,
                  RelationJoinRawNodeData.regionOrigin]
                exact Or.inr ⟨⟨region, root⟩, rfl, rfl⟩
                rw [step.checkedFragmentNode_data, data]
                simp [expectedPrefixNodeData_freshContent, data, root,
                  RelationJoinRawNodeData.regionOrigin,
                  RelationJoinRawNodeData.materialize, CNode.relocate,
                  CNode.region]
        · rcases requestOrigin with ⟨request, ⟨originExact⟩⟩
          subst origin
          have currentLanding : PrefixNodeLands
              (.snoc trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
                rfl sourceParametersExact)
              (prefixNodeFreshRequestOrigin step request)
              (step.checkedIdentityNode request) := by
            exact ⟨relationJoinConstructionNodeOrigins_get_checkedIdentityNode
              trace step rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl
                sourceParametersExact request⟩
          have targetExact := prefixNodeLands_functional landing currentLanding
          subst target
          refine ⟨currentLanding, step.checkedRegionImage step.sourceRegion,
            ?_, ?_⟩
          · simpa [expectedPrefixNodeData_freshRequest,
                RelationJoinRawNodeData.regionOrigin] using
              (prefixRegionLands_source _ step.sourceRegion)
          rw [expectedPrefixNodeData_freshRequest,
            step.checkedIdentityNode_data_at_sourceRegion]
          simp [RelationJoinRawNodeData.regionOrigin,
            RelationJoinRawNodeData.materialize]
termination_by steps _ _ _ _ _ _ _ _ _ _ => steps.length

/-- Terminal exhausted-wire deletion transports one exact prefix node row
and the landing of its neutral region carrier. -/
structure PlainPrefixNodeRowExact
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawNodeOrigin result)
    (target : result.plainFinal.val.NodeId) : Type where
  nodeLanding : RelationJoinRawOriginAtlas.PlainPrefixNodeLands
    result origin target
  regionTarget : result.plainFinal.val.RegionId
  regionLanding : plainPrefixRegionLands result
    (RelationJoinRawOriginAtlas.expectedPrefixNodeData
      result.steps origin.1).regionOrigin regionTarget
  dataExact : result.plainFinal.val.nodes target =
    (RelationJoinRawOriginAtlas.expectedPrefixNodeData
      result.steps origin.1).materialize regionTarget

def plainPrefixNodeLands_row_exact
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawNodeOrigin result)
    (target : result.plainFinal.val.NodeId)
    (landing : RelationJoinRawOriginAtlas.PlainPrefixNodeLands
      result origin target) :
    PlainPrefixNodeRowExact result origin target := by
  rcases landing with ⟨bound, boundLanding, rfl⟩
  have boundRow := prefixNodeLands_row_exact result.construction_trace
    origin.1 bound boundLanding
  refine ⟨⟨bound, boundLanding, rfl⟩,
    result.plainBoundRegionImage boundRow.regionTarget,
    ⟨boundRow.regionTarget, boundRow.regionLanding, rfl⟩, ?_⟩
  rw [result.plainBoundNodeImage_data, boundRow.dataExact]
  cases RelationJoinRawOriginAtlas.expectedPrefixNodeData
      result.steps origin.1 <;>
    simp [RelationJoinRawOriginAtlas.RelationJoinRawNodeData.materialize,
      CNode.relocate, CNode.region]

end ConcreteWireQuantifier.RelationJoinConstructionTrace

namespace RelationJoinRawOriginAtlas

open ConcreteWireQuantifier.RelationJoinConstructionTrace

/-- The executable node classifier agrees with every terminal construction
landing. -/
theorem ofResult_node_exact_of_plain_landing
    (result : RelationJoinResult source dying content parameters)
    {origin : RelationJoinRawNodeOrigin result}
    {target : result.plainFinal.val.NodeId}
    (landing : PlainPrefixNodeLands result origin target) :
    (ofResult result).nodeEquiv target = origin := by
  rcases landing with ⟨bound, boundLanding, rfl⟩
  rw [result.plainBoundNodeImage_eq_cast]
  exact ofResult_node_exact_of_landing result boundLanding

/-- The inverse atlas node row is exactly the unique terminal
construction-derived landing of that live neutral origin. -/
theorem ofResult_node_inverse_lands
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawNodeOrigin result) :
    PlainPrefixNodeLands result origin
      ((ofResult result).nodeEquiv.symm origin) := by
  obtain ⟨target, landing⟩ := plainPrefixNodeLands_total result origin
  have inverseExact : (ofResult result).nodeEquiv.symm origin = target := by
    apply (ofResult result).nodeEquiv.injective
    rw [(ofResult result).nodeEquiv.apply_symm_apply,
      ofResult_node_exact_of_plain_landing result landing]
  rw [inverseExact]
  exact landing

/-- Every atlas node row has exactly the independent source/content/request
payload, with its neutral region carrier classified by the region atlas. -/
theorem ofResult_node_data_exact
    (result : RelationJoinResult source dying content parameters)
    (origin : RelationJoinRawNodeOrigin result) :
    (match result.plainFinal.val.nodes
        ((ofResult result).nodeEquiv.symm origin) with
      | .atom region args =>
          RelationJoinRawNodeData.atom ((ofResult result).regionEquiv region)
            args
      | .ref region definition args =>
          RelationJoinRawNodeData.ref ((ofResult result).regionEquiv region)
            definition args
      | .identity region sig arity =>
          RelationJoinRawNodeData.identity
            ((ofResult result).regionEquiv region) sig arity) =
      expectedNodeData result origin := by
  have landing := ofResult_node_inverse_lands result origin
  have row :=
    ConcreteWireQuantifier.RelationJoinConstructionTrace.plainPrefixNodeLands_row_exact
      result origin _ landing
  have regionExact := ofResult_region_exact_of_landing result row.regionLanding
  have expectedExact := expectedPrefixNodeData_result result origin
  rw [← expectedExact, row.dataExact]
  cases data : expectedPrefixNodeData result.steps origin.1 with
  | atom region args =>
      simpa [data, RelationJoinRawNodeData.materialize] using
        congrArg (fun current => RelationJoinRawNodeData.atom current args)
          regionExact
  | ref region definition args =>
      simpa [data, RelationJoinRawNodeData.materialize] using
        congrArg
          (fun current => RelationJoinRawNodeData.ref current definition args)
          regionExact
  | identity region sig arity =>
      simpa [data, RelationJoinRawNodeData.materialize] using
        congrArg
          (fun current => RelationJoinRawNodeData.identity current sig arity)
          regionExact

end RelationJoinRawOriginAtlas

end RawNodeConformance

end MonolithicWireQuantifier

end VisualProof
