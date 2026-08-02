import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawOriginFacts

namespace VisualProof

namespace ConcreteWireQuantifier

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}

/-- Allocation-neutral region payload carried by one exact atlas row. -/
inductive AtlasRegionData (Region : Type)
  | sheet
  | cut (parent : Region)

/-- Allocation-neutral node payload carried by one exact atlas row. -/
inductive AtlasNodeData (Region : Type) (definitionCount : Nat)
  | atom (region : Region) (args : List Sig)
  | ref (region : Region) (definition : Fin definitionCount) (args : List Sig)
  | identity (region : Region) (sig : Sig) (arity : Nat)

/-- The prefix origin of a content region at one accepted occurrence.  The
content root is identified with the occurrence's source region. -/
def prefixContentRegionOrigin
    (steps : List (RelationJoinStep source dying content))
    (occurrence : Fin steps.length)
    (region : content.val.diagram.RegionId) :
    PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps :=
  if root : region = content.val.diagram.root then
    .inl (steps.get occurrence).sourceRegion
  else
    .inr ⟨occurrence, ⟨region, root⟩⟩

/-- Construction-owned region payload expected at one prefix origin. -/
def expectedRegionData
    (steps : List (RelationJoinStep source dying content)) :
    PrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps →
      AtlasRegionData (PrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps)
  | .inl region =>
      match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (.inl parent)
  | .inr ⟨occurrence, region⟩ =>
      match content.val.diagram.regions region.1 with
      | .sheet => .sheet
      | .cut parent =>
          .cut (prefixContentRegionOrigin steps occurrence parent)

/-- Construction-owned node payload expected at one prefix origin. -/
def expectedNodeData
    (steps : List (RelationJoinStep source dying content)) :
    PrefixNodeOrigin (source := source) (dying := dying)
        (content := content) steps →
      AtlasNodeData (PrefixRegionOrigin (source := source) (dying := dying)
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

/-- Read a checked region through its exact atlas carrier. -/
def AtlasRows.regionData
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (rows : AtlasRows (source := source) (dying := dying)
      (content := content) steps current)
    (target : current.val.RegionId) :
    AtlasRegionData (PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps) :=
  match current.val.regions target with
  | .sheet => .sheet
  | .cut parent => .cut (rows.regionAt parent)

/-- Read a checked node through its exact atlas region carrier. -/
def AtlasRows.nodeData
    {steps : List (RelationJoinStep source dying content)}
    {current : CheckedDiagram definitions}
    (rows : AtlasRows (source := source) (dying := dying)
      (content := content) steps current)
    (target : current.val.NodeId) :
    AtlasNodeData (PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps) definitions.length :=
  match current.val.nodes target with
  | .atom region args => .atom (rows.regionAt region) args
  | .ref region definition args =>
      .ref (rows.regionAt region) definition args
  | .identity region sig arity =>
      .identity (rows.regionAt region) sig arity

def liftAtlasRegionData
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    AtlasRegionData (PrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps) →
      AtlasRegionData (PrefixRegionOrigin (source := source) (dying := dying)
        (content := content) (steps ++ [step]))
  | .sheet => .sheet
  | .cut parent => .cut (liftRegionOrigin step parent)

def liftAtlasNodeData
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    AtlasNodeData (PrefixRegionOrigin (source := source) (dying := dying)
        (content := content) steps) definitions.length →
      AtlasNodeData (PrefixRegionOrigin (source := source) (dying := dying)
        (content := content) (steps ++ [step])) definitions.length
  | .atom region args => .atom (liftRegionOrigin step region) args
  | .ref region definition args =>
      .ref (liftRegionOrigin step region) definition args
  | .identity region sig arity =>
      .identity (liftRegionOrigin step region) sig arity

theorem expectedRegionData_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps) :
    expectedRegionData (steps ++ [step]) (liftRegionOrigin step origin) =
      liftAtlasRegionData step (expectedRegionData steps origin) := by
  cases origin with
  | inl region =>
      cases data : source.val.regions region <;>
        simp [expectedRegionData, liftRegionOrigin, liftAtlasRegionData, data]
  | inr occurrence =>
      rcases occurrence with ⟨occurrence, region⟩
      cases data : content.val.diagram.regions region.1 with
      | sheet =>
          simp [expectedRegionData, liftRegionOrigin, liftAtlasRegionData, data]
      | cut parent =>
          by_cases root : parent = content.val.diagram.root <;>
            simp [expectedRegionData, prefixContentRegionOrigin,
              liftRegionOrigin, liftAtlasRegionData, data, root]

theorem expectedRegionData_fresh
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    expectedRegionData (steps ++ [step]) (freshRegionOrigin step region) =
      match content.val.diagram.regions region.1 with
      | .sheet => .sheet
      | .cut parent =>
          .cut (if root : parent = content.val.diagram.root then
            .inl step.sourceRegion
          else
            freshRegionOrigin step ⟨parent, root⟩) := by
  cases data : content.val.diagram.regions region.1 <;>
    simp [expectedRegionData, prefixContentRegionOrigin,
      freshRegionOrigin, data]

theorem prefixContentRegionOrigin_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (occurrence : Fin steps.length)
    (region : content.val.diagram.RegionId) :
    prefixContentRegionOrigin (steps ++ [step])
        (Fin.cast (by simp) (Fin.castAdd 1 occurrence)) region =
      liftRegionOrigin step
        (prefixContentRegionOrigin steps occurrence region) := by
  by_cases root : region = content.val.diagram.root <;>
    simp [prefixContentRegionOrigin, root, liftRegionOrigin]

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

theorem expectedNodeData_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps) :
    expectedNodeData (steps ++ [step]) (liftNodeOrigin step origin) =
      liftAtlasNodeData step (expectedNodeData steps origin) := by
  cases origin with
  | inl node =>
      cases data : source.val.nodes node <;>
        simp [expectedNodeData, liftAtlasNodeData, liftNodeOrigin,
          liftRegionOrigin, data]
  | inr occurrence =>
      rcases occurrence with ⟨occurrence, node⟩
      cases node with
      | inl node =>
          cases data : content.val.diagram.nodes node <;>
            simp [expectedNodeData, liftAtlasNodeData, liftNodeOrigin,
              prefixContentRegionOrigin_lift, data]
      | inr request =>
          have stepExact : (steps ++ [step])[occurrence.val] =
              steps[occurrence.val] :=
            List.getElem_append_left occurrence.isLt
          simp [expectedNodeData, liftAtlasNodeData, liftNodeOrigin,
            liftRegionOrigin, stepExact]
          exact ⟨by simpa using
              identityRequest_sig_of_step_eq stepExact request,
            by simpa using
              identityRequest_arity_of_step_eq stepExact request⟩

theorem expectedNodeData_freshContent
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId) :
    expectedNodeData (steps ++ [step]) (freshContentNodeOrigin step node) =
      match content.val.diagram.nodes node with
      | .atom region args =>
          .atom (if root : region = content.val.diagram.root then
            .inl step.sourceRegion
          else freshRegionOrigin step ⟨region, root⟩) args
      | .ref region definition args =>
          .ref (if root : region = content.val.diagram.root then
            .inl step.sourceRegion
          else freshRegionOrigin step ⟨region, root⟩) definition args
      | .identity region sig arity =>
          .identity (if root : region = content.val.diagram.root then
            .inl step.sourceRegion
          else freshRegionOrigin step ⟨region, root⟩) sig arity := by
  cases data : content.val.diagram.nodes node <;>
    simp [expectedNodeData, freshContentNodeOrigin,
      prefixContentRegionOrigin, freshRegionOrigin, data]

theorem expectedNodeData_freshRequest
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length) :
    expectedNodeData (steps ++ [step]) (freshRequestNodeOrigin step request) =
      let requestData := step.attachment.identityRequests.get request
      .identity (.inl step.sourceRegion) requestData.sig
        requestData.attachments.length := by
  have stepExact : (steps ++ [step])[steps.length] = step :=
    List.getElem_concat_length rfl _
  simp [expectedNodeData, freshRequestNodeOrigin, stepExact]
  exact ⟨by simpa using identityRequest_sig_of_step_eq stepExact request,
    by simpa using identityRequest_arity_of_step_eq stepExact request⟩

@[simp] theorem decide_not_mem_singleton_eq_ne
    {count : Nat} (removed value : Fin count) :
    decide (value ∉ [removed]) = decide (value ≠ removed) := by
  by_cases same : value = removed <;> simp [same]

theorem DenseList.index_val_congr
    [DecidableEq α]
    {left right : List α}
    (same : left = right)
    (value : α)
    (leftMember : value ∈ left)
    (rightMember : value ∈ right) :
    (DenseList.index left value leftMember).val =
      (DenseList.index right value rightMember).val := by
  subst right
  rfl

theorem fragmentRegions_get_nonrootRegionPosition
    (step : RelationJoinStep source dying content)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    step.attachment.fragmentRegions.get (nonrootRegionPosition region) =
      region.1 := by
  have member : region.1 ∈ step.attachment.fragmentRegions := by
    simp [ConcreteSpliceAttachment.fragmentRegions,
      ConcreteDiagram.regionsList, Data.Finite.mem_allFin, region.2]
  let position := DenseList.index step.attachment.fragmentRegions region.1 member
  have positionVal : position.val = (nonrootRegionPosition region).val := by
    let retained :=
      (Data.Finite.allFin content.val.diagram.regionCount).filter
        (fun value => decide (value ∉ [content.val.diagram.root]))
    have rowsExact : step.attachment.fragmentRegions = retained := by
      unfold ConcreteSpliceAttachment.fragmentRegions
      simp only [ConcreteDiagram.regionsList]
      dsimp only [retained]
      congr 1
      funext value
      exact (decide_not_mem_singleton_eq_ne content.val.diagram.root value).symm
    have retainedMember : region.1 ∈ retained := by
      rw [← rowsExact]
      exact member
    have indexTransport :
        (DenseList.index step.attachment.fragmentRegions region.1 member).val =
          (DenseList.index retained region.1 retainedMember).val :=
      DenseList.index_val_congr rowsExact _ _ _
    rw [indexTransport]
    dsimp only [DenseList.index, retained, nonrootRegionPosition]
    exact retained_allFin_index_eq_dropFin_cast
      (fragmentRegionCount (content := content))
      content.val.diagram.root region.1 region.2
  have positionExact : position = nonrootRegionPosition region :=
    Fin.ext positionVal
  rw [← positionExact]
  exact DenseList.get_index _ _ _

theorem extendAtlas_regionAt_checkedFragmentRegion
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (prior : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step prior)
    (applicationLanding : NodeLands prior.rows (.inl step.application)
      step.priorApplication)
    (region : content.val.diagram.RegionId) :
    (extendAtlas step prior receipt applicationLanding).rows.regionAt
        (step.checkedFragmentRegion region) =
      if root : region = content.val.diagram.root then
        .inl step.sourceRegion
      else
        freshRegionOrigin step ⟨region, root⟩ := by
  by_cases root : region = content.val.diagram.root
  · simp only [root, dif_pos]
    rw [step.checkedFragmentRegion_root_eq_checkedRegionImage,
      ← extendAtlas_regionImageAgreement step prior receipt applicationLanding]
    exact ((extendAtlas step prior receipt applicationLanding).locateRegion
      (.inl step.sourceRegion)).2.exact
  · simp only [dif_neg root]
    let position := nonrootRegionPosition ⟨region, root⟩
    have targetExact : step.checkedFragmentRegion region =
        checkedFreshRegionAtPosition step position := by
      rw [checkedFreshRegionAtPosition_eq_checkedFragmentRegion]
      exact congrArg step.checkedFragmentRegion
        (fragmentRegions_get_nonrootRegionPosition step ⟨region, root⟩).symm
    rw [targetExact]
    change
      (extendRows step receipt.toAtlasStepCounts prior.rows).regionAt
          (checkedFreshRegionAtPosition step position) = _
    rw [extendRows_regionAt_fresh, nonrootRegionAt_position]

/-- Every checked region target carries exactly the construction-owned payload
named by its atlas row. -/
theorem RelationJoinConstructionTrace.regionData_exact
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
    (target : final.val.RegionId) :
    finalAtlas.rows.regionData target =
      expectedRegionData steps (finalAtlas.rows.regionAt target) := by
  induction trace with
  | nil =>
      cases data : source.val.regions target <;>
        simp [AtlasRows.regionData, expectedRegionData, initialAtlas, data]
  | @snoc steps step priorAtlas currentWireImage currentDying currentScope
      trace priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact receipt applicationLanding
      induction =>
      let rows := (extendAtlas step priorAtlas receipt applicationLanding).rows
      generalize originExact : rows.regionAt target = origin
      rcases regionOriginView step origin with priorCase | freshCase
      · rcases priorCase with ⟨priorOrigin, ⟨rfl⟩⟩
        obtain ⟨priorTarget, priorLanding⟩ :=
          priorAtlas.locateRegion priorOrigin
        have sameRow : rows.regionAt target =
            rows.regionAt (checkedRetainedRegion step priorTarget) := by
          rw [originExact]
          change liftRegionOrigin step priorOrigin =
            (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).regionAt
              (checkedRetainedRegion step priorTarget)
          rw [extendRows_regionAt_prior, priorLanding.exact]
        have targetExact : target = checkedRetainedRegion step priorTarget :=
          rows.regionAt_injective
            (extendAtlas step priorAtlas receipt applicationLanding).regionNodup
            sameRow
        subst target
        rw [expectedRegionData_lift]
        have priorDataExact := induction priorTarget
        cases data : step.prior.val.regions priorTarget with
        | sheet =>
            have expectedExact :
                expectedRegionData steps (priorAtlas.rows.regionAt priorTarget) =
                  .sheet := by
              rw [← priorDataExact]
              simp [AtlasRows.regionData, data]
            rw [← priorLanding.exact, expectedExact]
            simp only [liftAtlasRegionData]
            unfold AtlasRows.regionData
            rw [receipt.retainedRegionAllocation,
              step.checkedPriorRegion_sheet priorTarget data]
        | cut parent =>
            have expectedExact :
                expectedRegionData steps (priorAtlas.rows.regionAt priorTarget) =
                  .cut (priorAtlas.rows.regionAt parent) := by
              rw [← priorDataExact]
              simp [AtlasRows.regionData, data]
            rw [← priorLanding.exact, expectedExact]
            simp only [liftAtlasRegionData]
            unfold AtlasRows.regionData
            rw [receipt.retainedRegionAllocation,
              step.checkedPriorRegion_cut priorTarget parent data]
            change
              AtlasRegionData.cut
                  ((extendRows step receipt.toAtlasStepCounts priorAtlas.rows).regionAt
                    (step.checkedPriorRegion parent)) = _
            rw [← receipt.retainedRegionAllocation parent,
              extendRows_regionAt_prior]
      · rcases freshCase with ⟨region, ⟨rfl⟩⟩
        let position := nonrootRegionPosition region
        have sameRow : rows.regionAt target =
            rows.regionAt (checkedFreshRegionAtPosition step position) := by
          rw [originExact]
          change freshRegionOrigin step region =
            (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).regionAt
              (checkedFreshRegionAtPosition step position)
          rw [extendRows_regionAt_fresh, nonrootRegionAt_position]
        have targetExact : target = checkedFreshRegionAtPosition step position :=
          rows.regionAt_injective
            (extendAtlas step priorAtlas receipt applicationLanding).regionNodup
            sameRow
        subst target
        rw [expectedRegionData_fresh]
        have freshTarget :
            checkedFreshRegionAtPosition step position =
              step.checkedFragmentRegion region.1 := by
          rw [checkedFreshRegionAtPosition_eq_checkedFragmentRegion]
          exact congrArg step.checkedFragmentRegion
            (fragmentRegions_get_nonrootRegionPosition step region)
        rw [freshTarget]
        unfold AtlasRows.regionData
        cases data : content.val.diagram.regions region.1 with
        | sheet =>
            rw [step.checkedFragmentRegion_sheet region.1 region.2 data]
        | cut parent =>
            rw [step.checkedFragmentRegion_cut region.1 parent region.2 data]
            by_cases root : parent = content.val.diagram.root
            · simp only [root, dif_pos]
              rw [step.checkedFragmentRegion_root_eq_checkedRegionImage]
              change AtlasRegionData.cut
                  (rows.regionAt (step.checkedRegionImage step.sourceRegion)) = _
              rw [← extendAtlas_regionImageAgreement step priorAtlas receipt
                applicationLanding]
              exact congrArg AtlasRegionData.cut
                ((extendAtlas step priorAtlas receipt applicationLanding).locateRegion
                  (.inl step.sourceRegion)).2.exact
            · simp only [dif_neg root]
              let parentPosition := nonrootRegionPosition ⟨parent, root⟩
              have parentTarget :
                  step.checkedFragmentRegion parent =
                    checkedFreshRegionAtPosition step parentPosition := by
                rw [checkedFreshRegionAtPosition_eq_checkedFragmentRegion]
                exact congrArg step.checkedFragmentRegion
                  (fragmentRegions_get_nonrootRegionPosition step ⟨parent, root⟩).symm
              rw [parentTarget]
              change AtlasRegionData.cut
                  ((extendRows step receipt.toAtlasStepCounts priorAtlas.rows).regionAt
                    (checkedFreshRegionAtPosition step parentPosition)) = _
              rw [extendRows_regionAt_fresh, nonrootRegionAt_position]

/-- Every checked node target carries exactly the construction-owned payload
named by its atlas row, including its exact atlas region carrier. -/
theorem RelationJoinConstructionTrace.nodeData_exact
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
    (target : final.val.NodeId) :
    finalAtlas.rows.nodeData target =
      expectedNodeData steps (finalAtlas.rows.nodeAt target) := by
  induction trace with
  | nil =>
      cases data : source.val.nodes target <;>
        simp [AtlasRows.nodeData, expectedNodeData, initialAtlas, data]
  | @snoc steps step priorAtlas currentWireImage currentDying currentScope
      trace priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact receipt applicationLanding
      induction =>
      let atlas := extendAtlas step priorAtlas receipt applicationLanding
      let rows := atlas.rows
      generalize originExact : rows.nodeAt target = origin
      have originLive : PrefixNodeLive origin := by
        rw [← originExact]
        exact atlas.nodeRowsLive target
      rcases nodeOriginView step origin with priorCase | freshCase
      · rcases priorCase with ⟨priorOrigin, ⟨rfl⟩⟩
        have priorLive := liftNodeOrigin_live step priorOrigin originLive
        obtain ⟨priorTarget, priorLanding⟩ :=
          priorAtlas.locateNode priorOrigin priorLive
        have different : priorTarget ≠ step.priorApplication := by
          intro targetExact
          subst priorTarget
          have originIsApplication : priorOrigin = .inl step.application :=
            priorLanding.exact.symm.trans applicationLanding.exact
          subst priorOrigin
          simp [PrefixNodeLive, liftNodeOrigin] at originLive
        have sameRow : rows.nodeAt target =
            rows.nodeAt
              (checkedRetainedNode step receipt.toAtlasStepCounts
                priorTarget different) := by
          rw [originExact]
          change liftNodeOrigin step priorOrigin =
            (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).nodeAt
              (checkedRetainedNode step receipt.toAtlasStepCounts
                priorTarget different)
          rw [extendRows_nodeAt_prior, priorLanding.exact]
        have targetExact : target =
            checkedRetainedNode step receipt.toAtlasStepCounts
              priorTarget different :=
          rows.nodeAt_injective atlas.nodeNodup sameRow
        subst target
        rw [expectedNodeData_lift, ← priorLanding.exact,
          ← induction priorTarget]
        unfold AtlasRows.nodeData
        rw [receipt.retainedNodeAllocation,
          step.checkedPriorNode_data priorTarget different]
        cases data : step.prior.val.nodes priorTarget <;>
          simp only [CNode.relocate, liftAtlasNodeData]
        all_goals
          simp only [CNode.region]
          congr 1
          change
            (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).regionAt
                (step.checkedPriorRegion _) = _
          rw [← receipt.retainedRegionAllocation, extendRows_regionAt_prior]
      · rcases freshCase with contentCase | requestCase
        · rcases contentCase with ⟨node, ⟨rfl⟩⟩
          have sameRow : rows.nodeAt target =
              rows.nodeAt (step.checkedFragmentNode node) := by
            rw [originExact]
            change freshContentNodeOrigin step node =
              (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).nodeAt
                (step.checkedFragmentNode node)
            rw [extendRows_nodeAt_content]
          have targetExact : target = step.checkedFragmentNode node :=
            rows.nodeAt_injective atlas.nodeNodup sameRow
          subst target
          rw [expectedNodeData_freshContent]
          unfold AtlasRows.nodeData
          rw [step.checkedFragmentNode_data]
          cases data : content.val.diagram.nodes node <;>
            simp only [CNode.relocate]
          all_goals
            rw [extendAtlas_regionAt_checkedFragmentRegion]
            simp only [CNode.region]
        · rcases requestCase with ⟨request, ⟨rfl⟩⟩
          have sameRow : rows.nodeAt target =
              rows.nodeAt (step.checkedIdentityNode request) := by
            rw [originExact]
            change freshRequestNodeOrigin step request =
              (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).nodeAt
                (step.checkedIdentityNode request)
            rw [extendRows_nodeAt_request]
          have targetExact : target = step.checkedIdentityNode request :=
            rows.nodeAt_injective atlas.nodeNodup sameRow
          subst target
          rw [expectedNodeData_freshRequest]
          unfold AtlasRows.nodeData
          rw [step.checkedIdentityNode_data_at_sourceRegion]
          change AtlasNodeData.identity
              (atlas.rows.regionAt
                (step.checkedRegionImage step.sourceRegion)) _ _ = _
          rw [← extendAtlas_regionImageAgreement step priorAtlas receipt
            applicationLanding]
          exact congrArg
            (fun region => AtlasNodeData.identity region
              (step.attachment.identityRequests.get request).sig
              (step.attachment.identityRequests.get request).attachments.length)
            (atlas.locateRegion (.inl step.sourceRegion)).2.exact

/-- Read one terminal region through the direct final-origin cast. -/
def RelationJoinResult.plainRegionData
    {wire : source.val.WireId}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters)
    (target : result.plainFinal.val.RegionId) :
    AtlasRegionData (FinalRegionOrigin result) :=
  match result.plainFinal.val.regions target with
  | .sheet => .sheet
  | .cut parent => .cut (result.finalRegionOriginEquiv parent)

/-- Read one terminal node through the direct final-origin casts. -/
def RelationJoinResult.plainNodeData
    {wire : source.val.WireId}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters)
    (target : result.plainFinal.val.NodeId) :
    AtlasNodeData (FinalRegionOrigin result) definitions.length :=
  match result.plainFinal.val.nodes target with
  | .atom region args => .atom (result.finalRegionOriginEquiv region) args
  | .ref region definition args =>
      .ref (result.finalRegionOriginEquiv region) definition args
  | .identity region sig arity =>
      .identity (result.finalRegionOriginEquiv region) sig arity

/-- Terminal region payload conformance is the prefix theorem transported by
the direct inverse count cast; final exhausted-wire deletion changes no region
payload. -/
theorem RelationJoinResult.plainRegionData_exact
    {wire : source.val.WireId}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters)
    (target : result.plainFinal.val.RegionId) :
    result.plainRegionData target =
      expectedRegionData result.steps (result.finalRegionOriginEquiv target) := by
  let boundTarget : result.boundFinal.val.RegionId :=
    Fin.cast result.plainFinal_regionCount target
  have targetImage : result.plainBoundRegionImage boundTarget = target := by
    apply Fin.ext
    simp [boundTarget]
  have boundExact :=
    result.construction_trace.regionData_exact boundTarget
  change result.plainRegionData target =
    expectedRegionData result.steps
      (result.constructionAtlas.rows.regionAt boundTarget)
  cases data : result.boundFinal.val.regions boundTarget with
  | sheet =>
      have plainData := result.plainBoundRegionImage_sheet boundTarget data
      rw [targetImage] at plainData
      unfold RelationJoinResult.plainRegionData
      rw [plainData]
      unfold AtlasRows.regionData at boundExact
      rw [data] at boundExact
      exact boundExact
  | cut parent =>
      have plainData :=
        result.plainBoundRegionImage_cut boundTarget parent data
      rw [targetImage] at plainData
      have parentCast :
          Fin.cast result.plainFinal_regionCount
              (result.plainBoundRegionImage parent) = parent := by
        apply Fin.ext
        simp
      have parentOrigin :
          result.finalRegionOriginEquiv
              (result.plainBoundRegionImage parent) =
            result.constructionAtlas.rows.regionAt parent := by
        change result.constructionAtlas.rows.regionAt
            (Fin.cast result.plainFinal_regionCount
              (result.plainBoundRegionImage parent)) = _
        rw [parentCast]
      unfold RelationJoinResult.plainRegionData
      rw [plainData]
      simp only
      rw [parentOrigin]
      unfold AtlasRows.regionData at boundExact
      rw [data] at boundExact
      exact boundExact

/-- Terminal node payload conformance is the prefix theorem transported by
the direct inverse count cast; final exhausted-wire deletion changes only the
concrete region carrier, whose final-origin row is unchanged. -/
theorem RelationJoinResult.plainNodeData_exact
    {wire : source.val.WireId}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters)
    (target : result.plainFinal.val.NodeId) :
    result.plainNodeData target =
      expectedNodeData result.steps (result.finalNodeOriginEquiv target).1 := by
  let boundTarget : result.boundFinal.val.NodeId :=
    Fin.cast result.plainFinal_nodeCount target
  have targetImage : result.plainBoundNodeImage boundTarget = target := by
    rw [result.plainBoundNodeImage_eq_cast]
    apply Fin.ext
    rfl
  have boundExact :=
    result.construction_trace.nodeData_exact boundTarget
  change result.plainNodeData target =
    expectedNodeData result.steps
      (result.constructionAtlas.rows.nodeAt boundTarget)
  have plainData := result.plainBoundNodeImage_data boundTarget
  rw [targetImage] at plainData
  cases data : result.boundFinal.val.nodes boundTarget with
  | atom region nodeArgs =>
      rw [data] at plainData
      simp only [CNode.region, CNode.relocate] at plainData
      have regionCast :
          Fin.cast result.plainFinal_regionCount
              (result.plainBoundRegionImage region) = region := by
        apply Fin.ext
        simp
      have regionOrigin :
          result.finalRegionOriginEquiv
              (result.plainBoundRegionImage region) =
            result.constructionAtlas.rows.regionAt region := by
        change result.constructionAtlas.rows.regionAt
            (Fin.cast result.plainFinal_regionCount
              (result.plainBoundRegionImage region)) = _
        rw [regionCast]
      unfold RelationJoinResult.plainNodeData
      rw [plainData]
      simp only
      rw [regionOrigin]
      unfold AtlasRows.nodeData at boundExact
      rw [data] at boundExact
      simpa only using boundExact
  | ref region definition nodeArgs =>
      rw [data] at plainData
      simp only [CNode.region, CNode.relocate] at plainData
      have regionCast :
          Fin.cast result.plainFinal_regionCount
              (result.plainBoundRegionImage region) = region := by
        apply Fin.ext
        simp
      have regionOrigin :
          result.finalRegionOriginEquiv
              (result.plainBoundRegionImage region) =
            result.constructionAtlas.rows.regionAt region := by
        change result.constructionAtlas.rows.regionAt
            (Fin.cast result.plainFinal_regionCount
              (result.plainBoundRegionImage region)) = _
        rw [regionCast]
      unfold RelationJoinResult.plainNodeData
      rw [plainData]
      simp only
      rw [regionOrigin]
      unfold AtlasRows.nodeData at boundExact
      rw [data] at boundExact
      simpa only using boundExact
  | identity region sig arity =>
      rw [data] at plainData
      simp only [CNode.region, CNode.relocate] at plainData
      have regionCast :
          Fin.cast result.plainFinal_regionCount
              (result.plainBoundRegionImage region) = region := by
        apply Fin.ext
        simp
      have regionOrigin :
          result.finalRegionOriginEquiv
              (result.plainBoundRegionImage region) =
            result.constructionAtlas.rows.regionAt region := by
        change result.constructionAtlas.rows.regionAt
            (Fin.cast result.plainFinal_regionCount
              (result.plainBoundRegionImage region)) = _
        rw [regionCast]
      unfold RelationJoinResult.plainNodeData
      rw [plainData]
      simp only
      rw [regionOrigin]
      unfold AtlasRows.nodeData at boundExact
      rw [data] at boundExact
      simpa only using boundExact

end ConcreteWireQuantifier

end VisualProof
