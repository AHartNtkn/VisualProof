import VisualProof.Rule.MonolithicWireQuantifierCore

namespace VisualProof

universe u

namespace MonolithicWireQuantifier

namespace Internal

/-- Nil case of the batch reconstruction fold: only sever-retained carriers
have representatives before the first occurrence is restored. -/
def batchReconstructionNil
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites) :
    BatchReconstructionState (pattern := pattern) sites [] result.checked
      result.checked where
  regionImage := fun region =>
    result.regionImage region.1 (by
      have retained :
          region.1 ∉
            sites.flatMap
              ConcreteWireQuantifier.RelationSeverSite.removedRegions := by
        simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
          using region.2
      exact (result.retainedRegion_iff region.1).mpr retained)
  regionImage_injective := by
    intro left right same
    apply Subtype.ext
    apply denseIndex_injective
      (ConcreteWireQuantifier.Internal.retainedRegions source
        (sites.flatMap
          ConcreteWireQuantifier.RelationSeverSite.removedRegions))
      (by
        exact (result.retainedRegion_iff left.1).mpr (by
          simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
            using left.2))
      (by
        exact (result.retainedRegion_iff right.1).mpr (by
          simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
            using right.2))
    apply Fin.ext
    simpa using congrArg Fin.val same
  retainedRegionImage_val := by
    intro region retained
    rfl
  regionParentCovered := by
    intro region parent data
    apply Or.inl
    have regionRetained := (result.retainedRegion_iff region.1).mpr (by
      simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
        using region.2)
    exact (result.retainedRegion_iff parent).mp
      (result.regionParent_survives region.1 regionRetained parent data)
  regionSheetExact := by
    intro region data
    apply result.regionImage_sheet region.1
      ((result.retainedRegion_iff region.1).mpr (by
        simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
          using region.2))
    exact data
  regionCutExact := by
    intro region parent data
    apply result.regionImage_cut region.1
      ((result.retainedRegion_iff region.1).mpr (by
        simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
          using region.2))
      parent data
  nodeImage := fun node =>
    result.nodeImage node.1 (by
      have retained :
          node.1 ∉
            sites.flatMap
              ConcreteWireQuantifier.RelationSeverSite.removedNodes := by
        simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
          using node.2
      exact (result.retainedNode_iff node.1).mpr retained)
  nodeImage_injective := by
    intro left right same
    apply Subtype.ext
    apply denseIndex_injective
      (ConcreteWireQuantifier.Internal.retainedNodes source
        (sites.flatMap
          ConcreteWireQuantifier.RelationSeverSite.removedNodes))
      (by
        exact (result.retainedNode_iff left.1).mpr (by
          simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
            using left.2))
      (by
        exact (result.retainedNode_iff right.1).mpr (by
          simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
            using right.2))
    apply Fin.ext
    simpa using congrArg Fin.val same
  nodeRegionCovered := by
    intro node
    apply Or.inl
    have nodeRetained := (result.retainedNode_iff node.1).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2)
    exact (result.retainedRegion_iff _).mp
      (result.nodeRegion_survives node.1 nodeRetained)
  nodeTableExact := by
    intro node
    have nodeRetained := (result.retainedNode_iff node.1).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2)
    exact result.nodeImage_data node.1 nodeRetained
  portImage := fun _ => Data.Finite.FiniteEquiv.refl CPort
  portImageCorresponds := by
    intro node port required
    have nodeRetained := (result.retainedNode_iff node.1).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2)
    rw [result.nodeImage_data node.1 nodeRetained]
    exact portDataCorresponds_refl_relocate
      source.val node.1 _ port required
  portImageRequired := by
    intro node port
    have nodeRetained := (result.retainedNode_iff node.1).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2)
    rw [result.nodeImage_data node.1 nodeRetained]
    simp
  wireImage := fun wire =>
    result.wireImage wire.1 (by
      have retained :
          wire.1 ∉
            sites.flatMap
              ConcreteWireQuantifier.RelationSeverSite.removedWires := by
        simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
          using wire.2
      exact (result.retainedWire_iff wire.1).mpr retained)
  wireImage_injective := by
    intro left right same
    apply Subtype.ext
    apply denseIndex_injective
      (ConcreteWireQuantifier.Internal.retainedWires source
        (sites.flatMap
          ConcreteWireQuantifier.RelationSeverSite.removedWires))
      (by
        exact (result.retainedWire_iff left.1).mpr (by
          simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
            using left.2))
      (by
        exact (result.retainedWire_iff right.1).mpr (by
          simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
            using right.2))
    apply Fin.ext
    simpa using congrArg Fin.val same
  retainedWireImage_val := by
    intro wire retained
    rfl
  wireScopeCovered := by
    intro wire
    apply Or.inl
    have wireRetained := (result.retainedWire_iff wire.1).mpr (by
      simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
        using wire.2)
    exact (result.retainedRegion_iff _).mp
      (result.wireScope_survives wire.1 wireRetained)
  wireSignatureExact := by
    intro wire
    exact result.wireImage_signature wire.1
      ((result.retainedWire_iff wire.1).mpr (by
        simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
          using wire.2))
  wireScopeExact := by
    intro wire
    exact result.wireImage_scope wire.1
      ((result.retainedWire_iff wire.1).mpr (by
        simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
          using wire.2))
  wireEndpointForward := by
    intro wire endpoint incident nodeCovered
    have wireRetained := (result.retainedWire_iff wire.1).mpr (by
      simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
        using wire.2)
    have nodeRetained := (result.retainedNode_iff endpoint.node).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using nodeCovered)
    exact result.wireImage_endpoint_mem wire.1 wireRetained endpoint
      nodeRetained incident
  joinNodeImage := fun node => some node
  pendingOrigins := result.atoms
  pendingApplications := result.atoms
  pendingApplicationsExact := by simp
  representedNodesAvoidPending := by
    intro node pending
    have retained :
        node.1 ∉
          sites.flatMap
            ConcreteWireQuantifier.RelationSeverSite.removedNodes := by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2
    have retainedMember := (result.retainedNode_iff node.1).mpr retained
    unfold ConcreteWireQuantifier.RelationSeverResult.atoms at pending
    rcases List.mem_map.mp pending with ⟨site, _siteMember, atomExact⟩
    have values := congrArg Fin.val atomExact
    rw [result.atom_val] at values
    rw [result.nodeImage_val node.1 retainedMember] at values
    have imageBound :=
      result.nodeImage_lt_retainedCount node.1 retainedMember
    omega

theorem newlyCoveredRegion
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {restored : List (ContentOccurrence source pattern)}
    (content : ContentOccurrence source pattern)
    (region : source.val.RegionId)
    (covered : BatchCoveredRegion sites (restored ++ [content]) region)
    (notOld : ¬ BatchCoveredRegion sites restored region) :
    ∃ patternRegion,
      patternRegion ≠ pattern.val.diagram.root ∧
        content.occurrence.regionMap patternRegion = region := by
  rcases covered with retained | restoredAll
  · exact False.elim (notOld (Or.inl retained))
  · rcases restoredAll with
      ⟨candidate, member, patternRegion, nonroot, mapped⟩
    rcases List.mem_append.mp member with previous | final
    · exact False.elim
        (notOld (Or.inr
          ⟨candidate, previous, patternRegion, nonroot, mapped⟩))
    · have candidateExact : candidate = content := by simpa using final
      subst candidate
      exact ⟨patternRegion, nonroot, mapped⟩

theorem newlyCoveredNode
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {restored : List (ContentOccurrence source pattern)}
    (content : ContentOccurrence source pattern)
    (node : source.val.NodeId)
    (covered : BatchCoveredNode sites (restored ++ [content]) node)
    (notOld : ¬ BatchCoveredNode sites restored node) :
    ∃ patternNode, content.occurrence.nodeMap patternNode = node := by
  rcases covered with retained | restoredAll
  · exact False.elim (notOld (Or.inl retained))
  · rcases restoredAll with ⟨candidate, member, patternNode, mapped⟩
    rcases List.mem_append.mp member with previous | final
    · exact False.elim
        (notOld (Or.inr ⟨candidate, previous, patternNode, mapped⟩))
    · have candidateExact : candidate = content := by simpa using final
      subst candidate
      exact ⟨patternNode, mapped⟩

theorem newlyCoveredWire
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {restored : List (ContentOccurrence source pattern)}
    (content : ContentOccurrence source pattern)
    (wire : source.val.WireId)
    (covered : BatchCoveredWire sites (restored ++ [content]) wire)
    (notOld : ¬ BatchCoveredWire sites restored wire) :
    ∃ patternWire,
      patternWire ∉ pattern.val.boundary ∧
        content.occurrence.wireMap patternWire = wire := by
  rcases covered with retained | restoredAll
  · exact False.elim (notOld (Or.inl retained))
  · rcases restoredAll with
      ⟨candidate, member, patternWire, internal, mapped⟩
    rcases List.mem_append.mp member with previous | final
    · exact False.elim
        (notOld (Or.inr
          ⟨candidate, previous, patternWire, internal, mapped⟩))
    · have candidateExact : candidate = content := by simpa using final
      subst candidate
      exact ⟨patternWire, internal, mapped⟩

/-- A successful option-valued list traversal retains exact positional
ownership; consumers need not inspect the traversal implementation again. -/
theorem optionMapM_eq_some_length_get
    {α β : Type}
    (transform : α → Option β)
    {source : List α}
    {target : List β}
    (accepted : source.mapM transform = some target) :
    ∃ exactLength : source.length = target.length,
      ∀ position : Fin source.length,
        transform (source.get position) =
          some (target.get (Fin.cast exactLength position)) := by
  induction source generalizing target with
  | nil =>
      simp at accepted
      subst target
      refine ⟨rfl, ?_⟩
      intro position
      exact Fin.elim0 position
  | cons head tail induction =>
      cases headExact : transform head with
      | none => simp [List.mapM_cons, headExact] at accepted
      | some image =>
          cases tailExact : tail.mapM transform with
          | none => simp [List.mapM_cons, headExact, tailExact] at accepted
          | some images =>
              simp [List.mapM_cons, headExact, tailExact] at accepted
              subst target
              obtain ⟨tailLength, tailEvidence⟩ := induction tailExact
              refine ⟨by simp [tailLength], ?_⟩
              intro position
              refine Fin.cases ?_ (fun rest => ?_) position
              · simpa using headExact
              · simpa [List.get_eq_getElem, tailLength] using
                  tailEvidence rest

theorem optionMapM_eq_some_of_pointwise
    {α β : Type}
    (transform : α → Option β)
    (image : α → β)
    (values : List α)
    (pointwise : ∀ value, value ∈ values →
      transform value = some (image value)) :
    values.mapM transform = some (values.map image) := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.mapM_cons, pointwise head (by simp)]
      rw [induction (fun value member => pointwise value (by simp [member]))]
      rfl

/-- The sever result transports one site's ordered formal vector exactly to
the stored formal-image vector. -/
theorem relationSeverSiteFormals_mapM
    {source : CheckedDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    (sites.get site).formals.mapM result.wireImage? =
      some (result.siteFormalImages site) := by
  let survives :
      ∀ wire, wire ∈ (sites.get site).formals →
        wire ∈ ConcreteWireQuantifier.Internal.retainedWires source
          (sites.flatMap
            ConcreteWireQuantifier.RelationSeverSite.removedWires) :=
    fun wire member => by
      obtain ⟨position, rfl⟩ := List.get_of_mem member
      exact result.siteFormal_survives site position
  let image : source.val.WireId → result.checked.val.WireId :=
    fun wire =>
      if member : wire ∈ (sites.get site).formals then
        result.wireImage wire (survives wire member)
      else
        result.relationWire
  have pointwise :
      ∀ wire, wire ∈ (sites.get site).formals →
        result.wireImage? wire = some (image wire) := by
    intro wire member
    have imageExact :
        image wire = result.wireImage wire (survives wire member) := by
      unfold image
      rw [dif_pos member]
    rw [imageExact]
    simp [ConcreteWireQuantifier.RelationSeverResult.wireImage?,
      survives wire member]
  rw [optionMapM_eq_some_of_pointwise result.wireImage? image _ pointwise]
  congr 1
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    rw [result.siteFormalImages_get site ⟨index, rightBound⟩]
    simp [List.get_eq_getElem, image]

/-- Every retained semantic step carries the batch-wide relation signature
and ambient parameter vector fixed by its accepted trace. -/
theorem relationJoinTrace_step_exact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List
      (ConcreteWireQuantifier.RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {regionImage : source.val.RegionId → final.val.RegionId}
    {nodeImage : source.val.NodeId → Option final.val.NodeId}
    {wireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : ConcreteWireQuantifier.RelationJoinSemanticTrace
      source dying content parameters args steps final regionImage nodeImage
        wireImage finalDying finalScope)
    (step : ConcreteWireQuantifier.RelationJoinStep source dying content)
    (member : step ∈ steps) :
    step.relationArgs = args ∧ step.sourceParameters = parameters := by
  induction trace with
  | nil => simp at member
  | snoc trace finalStep priorExact priorRegionExact priorNodeExact
      priorWireExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      rcases List.mem_append.mp member with previous | final
      · exact induction previous
      · have stepExact : step = finalStep := by simpa using final
        subst step
        exact ⟨relationArgsExact, sourceParametersExact⟩

theorem relationJoinTrace_count_exact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List
      (ConcreteWireQuantifier.RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {regionImage : source.val.RegionId → final.val.RegionId}
    {nodeImage : source.val.NodeId → Option final.val.NodeId}
    {wireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : ConcreteWireQuantifier.RelationJoinSemanticTrace
      source dying content parameters args steps final regionImage nodeImage
        wireImage finalDying finalScope)
    (identitiesEmpty : ∀ step ∈ steps,
      step.attachment.identityRequests = []) :
    final.val.regionCount = source.val.regionCount +
        steps.length *
          (content.val.diagram.regionsList.filter fun region =>
            decide (region ≠ content.val.diagram.root)).length ∧
      final.val.nodeCount + steps.length = source.val.nodeCount +
        steps.length * content.val.diagram.nodeCount ∧
      final.val.wireCount = source.val.wireCount +
        steps.length *
          (content.val.diagram.wiresList.filter fun wire =>
            decide (wire ∉ content.val.boundary)).length := by
  induction trace with
  | nil => simp
  | snoc trace step priorExact priorRegionExact priorNodeExact priorWireExact
      priorDyingExact priorScopeExact relationArgsExact sourceParametersExact
      induction =>
      cases priorExact
      have stepIdentities : step.attachment.identityRequests = [] :=
        identitiesEmpty step (by simp)
      rcases induction (fun prior member =>
        identitiesEmpty prior (List.mem_append_left _ member)) with
        ⟨regionsExact, nodesExact, wiresExact⟩
      simp only [decide_not] at *
      constructor
      · have stepRegions := step.checked_regionCount
        change step.checked.val.regionCount = step.prior.val.regionCount +
          (content.val.diagram.regionsList.filter fun region =>
            decide (region ≠ content.val.diagram.root)).length at stepRegions
        simp only [decide_not] at stepRegions
        simp only [List.length_append, List.length_singleton] at *
        simp [Nat.add_mul]
        omega
      · constructor
        · have stepNodes := step.checked_nodeCount_add_one
          simp [stepIdentities] at stepNodes
          simp only [List.length_append, List.length_singleton] at *
          simp [Nat.add_mul]
          omega
        · have stepWires := step.checked_wireCount
          change step.checked.val.wireCount = step.prior.val.wireCount +
            (content.val.diagram.wiresList.filter fun wire =>
              decide (wire ∉ content.val.boundary)).length at stepWires
          simp only [decide_not] at stepWires
          simp only [List.length_append, List.length_singleton] at *
          simp [Nat.add_mul]
          omega

/-- Positional alignment between one inverse join step and the original
checked occurrence restored at that step. -/
structure InverseStepOccurrenceAlignment
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    {dying : result.checked.val.WireId}
    (step : ConcreteWireQuantifier.RelationJoinStep
      result.checked dying pattern)
    (content : ContentOccurrence source pattern) where
  site : Fin sites.length
  siteExact : sites.get site = content.toConcreteSite
  applicationExact : step.application = result.atom site
  boundarySurvives :
    ∀ position : Fin pattern.val.boundary.length,
      content.occurrence.wireMap (pattern.val.boundary.get position) ∈
        ConcreteWireQuantifier.Internal.retainedWires source
          (sites.flatMap
            ConcreteWireQuantifier.RelationSeverSite.removedWires)
  sourceAttachmentExact :
    ∀ position : Fin pattern.val.boundary.length,
      step.sourceAttachments.get
          (Fin.cast step.sourceAttachmentArity.symm position) =
        result.wireImage
          (content.occurrence.wireMap
            (pattern.val.boundary.get position))
          (boundarySurvives position)

theorem inverseStep_sourceArguments_exact
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    {dying : result.checked.val.WireId}
    (step : ConcreteWireQuantifier.RelationJoinStep
      result.checked dying pattern)
    (site : Fin sites.length)
    (applicationExact : step.application = result.atom site)
    (arityExact :
      (sites.get site).formals.length = step.relationArgs.length) :
    step.sourceArguments = result.siteFormalImages site := by
  have sourceLength :=
    ConcreteWireQuantifier.relationArgumentWires?_length result.checked
      step.application step.relationArgs 0 step.sourceArguments
        step.sourceArgumentsAccepted
  apply List.ext_get
  · calc
      step.sourceArguments.length = step.relationArgs.length := sourceLength
      _ = (sites.get site).formals.length := arityExact.symm
      _ = (result.siteFormalImages site).length :=
        (result.siteFormalImages_length site).symm
  · intro index sourceBound targetBound
    let argumentPosition : Fin step.relationArgs.length :=
      ⟨index, by simpa [sourceLength] using sourceBound⟩
    let formalPosition : Fin (sites.get site).formals.length :=
      Fin.cast arityExact.symm argumentPosition
    have sourceOwner :=
      ConcreteWireQuantifier.relationArgumentWires?_owner result.checked
        step.application step.relationArgs 0 step.sourceArguments
          step.sourceArgumentsAccepted argumentPosition
    have formalOwner :
        result.checked.val.endpointOwner?
            ⟨result.atom site, .arg formalPosition.val⟩ =
          some
            (result.wireImage
              ((sites.get site).formals.get formalPosition)
              (result.siteFormal_survives site formalPosition)) :=
      have incident := result.atomArgument_incident site formalPosition
      have required :=
        ConcreteDiagram.incident_port_required definitions
          result.checked.val result.checked.property _ _ incident
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions
        result.checked.val result.checked.property _ _ required _ incident
    have sourceOwnerAtAtom :
        result.checked.val.endpointOwner?
            ⟨result.atom site, .arg argumentPosition.val⟩ =
          some
            (step.sourceArguments.get
              (Fin.cast sourceLength.symm argumentPosition)) := by
      simpa only [applicationExact, Nat.zero_add] using sourceOwner
    have ownerSame := Option.some.inj (sourceOwnerAtAtom.symm.trans (by
      simpa [argumentPosition, formalPosition] using formalOwner))
    rw [result.siteFormalImages_get site ⟨index, targetBound⟩]
    simpa [argumentPosition, formalPosition, List.get_eq_getElem] using
      ownerSame

/-- The checker-owned occurrence evidence and accepted sever transport
determine the complete source attachment vector for its paired inverse step. -/
noncomputable def inverseStepOccurrenceAlignmentOfChecked
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (first content : ContentOccurrence source pattern)
    (checked : CheckedOccurrence scope first content)
    (parameters : List result.checked.val.WireId)
    (parametersAccepted :
      first.parameters.mapM result.wireImage? = some parameters)
    {dying : result.checked.val.WireId}
    (step : ConcreteWireQuantifier.RelationJoinStep
      result.checked dying pattern)
    (site : Fin sites.length)
    (siteExact : sites.get site = content.toConcreteSite)
    (applicationExact : step.application = result.atom site)
    (arityExact :
      (sites.get site).formals.length = step.relationArgs.length)
    (sourceParametersExact : step.sourceParameters = parameters) :
    InverseStepOccurrenceAlignment result step content := by
  have siteFormalsExact :
      (sites.get site).formals = content.formals := by
    exact congrArg
      ConcreteWireQuantifier.RelationSeverSite.formals siteExact
  have sourceArgumentsExact :=
    inverseStep_sourceArguments_exact result step site applicationExact
      arityExact
  have formalsAccepted :
      content.formals.mapM result.wireImage? =
        some step.sourceArguments := by
    calc
      content.formals.mapM result.wireImage? =
          (sites.get site).formals.mapM result.wireImage? := by
        rw [siteFormalsExact]
      _ = some (result.siteFormalImages site) :=
        relationSeverSiteFormals_mapM result site
      _ = some step.sourceArguments := congrArg some sourceArgumentsExact.symm
  have contentParametersAccepted :
      content.parameters.mapM result.wireImage? = some parameters := by
    rw [checked.parametersExact, parametersAccepted]
  have boundaryAccepted :
      content.occurrence.boundaryAttachments.mapM result.wireImage? =
        some step.sourceAttachments := by
    calc
      content.occurrence.boundaryAttachments.mapM result.wireImage? =
          (content.formals ++ content.parameters).mapM result.wireImage? :=
        congrArg (fun wires => wires.mapM result.wireImage?)
          checked.boundaryExact
      _ = some (step.sourceArguments ++ step.sourceParameters) := by
        rw [List.mapM_append, formalsAccepted,
          contentParametersAccepted, sourceParametersExact]
        rfl
      _ = some step.sourceAttachments :=
        congrArg some step.sourceAttachmentsExact.symm
  let boundaryEvidence :=
    optionMapM_eq_some_length_get result.wireImage? boundaryAccepted
  let boundaryLength := boundaryEvidence.choose
  have boundaryGet := boundaryEvidence.choose_spec
  have boundaryLanding :
      ∀ position : Fin pattern.val.boundary.length,
        ∃ survives :
            content.occurrence.wireMap
                (pattern.val.boundary.get position) ∈
              ConcreteWireQuantifier.Internal.retainedWires source
                (sites.flatMap
                  ConcreteWireQuantifier.RelationSeverSite.removedWires),
          result.wireImage
              (content.occurrence.wireMap
                (pattern.val.boundary.get position)) survives =
            step.sourceAttachments.get
              (Fin.cast step.sourceAttachmentArity.symm position) := by
    intro position
    let sourcePosition :
        Fin content.occurrence.boundaryAttachments.length :=
      Fin.cast content.occurrence.boundaryAttachments_length.symm position
    have transported := boundaryGet sourcePosition
    have sourceGet :
        content.occurrence.boundaryAttachments.get sourcePosition =
          content.occurrence.wireMap
            (pattern.val.boundary.get position) := by
      simp [sourcePosition, Occurrence.boundaryAttachments,
        List.get_eq_getElem]
    have targetPosition :
        Fin.cast boundaryLength sourcePosition =
          Fin.cast step.sourceAttachmentArity.symm position := by
      apply Fin.ext
      rfl
    rw [sourceGet, targetPosition] at transported
    unfold ConcreteWireQuantifier.RelationSeverResult.wireImage? at transported
    split at transported
    · rename_i survives
      exact ⟨by simpa using survives, Option.some.inj transported⟩
    · simp at transported
  exact
    { site := site
      siteExact := siteExact
      applicationExact := applicationExact
      boundarySurvives := fun position => (boundaryLanding position).choose
      sourceAttachmentExact := fun position =>
        (boundaryLanding position).choose_spec.symm }

theorem InverseStepOccurrenceAlignment.identityRequestsEmpty
    (alignment : InverseStepOccurrenceAlignment result step content) :
    step.attachment.identityRequests = [] := by
  apply step.identityRequests_eq_nil_of_sourceAttachments_coherent
  intro left right same
  rw [alignment.sourceAttachmentExact, alignment.sourceAttachmentExact]
  apply Fin.ext
  simp only [ConcreteWireQuantifier.RelationSeverResult.wireImage_val]
  have mapped := congrArg content.occurrence.wireMap same
  have mappedGetElem := mapped
  simp only [List.get_eq_getElem] at mappedGetElem
  unfold ConcreteWireQuantifier.Internal.retainedWireIndex DenseList.index
  simp [mappedGetElem]

theorem RelationSeverConcreteReceipt.inverseSteps_sites_length
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    receipt.inverse.steps.length =
      (receipt.extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site).length := by
  calc
    receipt.inverse.steps.length =
        (receipt.inverse.steps.map
          ConcreteWireQuantifier.RelationJoinStep.application).length := by
      simp
    _ = receipt.result.atoms.length :=
      congrArg List.length receipt.inverseStepsExact
    _ =
        (receipt.extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).length := by
      simp [ConcreteWireQuantifier.RelationSeverResult.atoms,
        Data.Finite.allFin_eq_finRange]

theorem RelationSeverConcreteReceipt.sites_occurrences_length
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    (receipt.extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site).length =
      occurrences.length := by
  simpa using congrArg List.length
    receipt.extractions.entries.semanticEvidence_sites

/-- Every retained inverse step is paired, at the same accepted list
position, with the checker-owned original occurrence it restores. -/
noncomputable def RelationSeverConcreteReceipt.inverseStepAlignment
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (position : Fin receipt.inverse.steps.length) :
    let sites :=
      receipt.extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site
    let steps := receipt.inverse.steps
    let stepsSitesLength : steps.length = sites.length :=
      receipt.inverseSteps_sites_length
    let sitesContentsLength : sites.length = occurrences.length :=
      receipt.sites_occurrences_length
    let site := Fin.cast stepsSitesLength position
    let contentPosition :=
      Fin.cast (stepsSitesLength.trans sitesContentsLength) position
    InverseStepOccurrenceAlignment receipt.result (steps.get position)
      (occurrences.get contentPosition) := by
  dsimp only
  let sites :=
    receipt.extractions.semanticEvidence.map
      WireQuantifierSemantics.RelationSeverOccurrence.site
  let steps := receipt.inverse.steps
  have sitesExact : sites = occurrences.map ContentOccurrence.toConcreteSite :=
    receipt.extractions.entries.semanticEvidence_sites
  have stepsSitesLength : steps.length = sites.length :=
    receipt.inverseSteps_sites_length
  have sitesContentsLength : sites.length = occurrences.length :=
    receipt.sites_occurrences_length
  let site : Fin sites.length := Fin.cast stepsSitesLength position
  let contentPosition : Fin occurrences.length :=
    Fin.cast (stepsSitesLength.trans sitesContentsLength) position
  let step := steps.get position
  let content := occurrences.get contentPosition
  have siteExact : sites.get site = content.toConcreteSite := by
    have atPosition := congrArg (fun values => values[site.val]?) sitesExact
    change sites[site.val]? =
      (occurrences.map ContentOccurrence.toConcreteSite)[site.val]?
        at atPosition
    have siteAt : sites[site.val]? = some (sites.get site) := by
      simp [List.getElem?_eq_getElem, site.isLt]
    have indexExact : site.val = contentPosition.val := rfl
    have contentAt : occurrences[site.val]? = some content := by
      rw [indexExact]
      simp [content, List.getElem?_eq_getElem, contentPosition.isLt]
    rw [siteAt, List.getElem?_map, contentAt] at atPosition
    exact Option.some.inj (by simpa using atPosition)
  have applicationExact : step.application = receipt.result.atom site := by
    have applicationsAt := congrArg
      (fun applications => applications[position.val]?)
      receipt.inverseStepsExact
    change
      (steps.map
        ConcreteWireQuantifier.RelationJoinStep.application)[position.val]? =
        receipt.result.atoms[position.val]? at applicationsAt
    have stepAt :
        (steps.map
          ConcreteWireQuantifier.RelationJoinStep.application)[position.val]? =
          some step.application := by
      simp [step, steps, List.getElem?_eq_getElem, position.isLt]
    have positionLtSites : position.val < sites.length := by
      rw [← stepsSitesLength]
      simpa [steps] using position.isLt
    have siteAt :
        (Data.Finite.allFin sites.length)[position.val]? = some site := by
      rw [Data.Finite.allFin_eq_finRange]
      have atPosition :
          (List.finRange sites.length)[position.val]? =
            some ⟨position.val, positionLtSites⟩ := by
        simp [positionLtSites]
      rw [atPosition]
      congr 2
    rw [stepAt] at applicationsAt
    change
      some step.application =
        ((Data.Finite.allFin sites.length).map
          receipt.result.atom)[position.val]? at applicationsAt
    rw [List.getElem?_map, siteAt] at applicationsAt
    exact Option.some.inj applicationsAt
  have stepExact := relationJoinTrace_step_exact
    receipt.inverse.semantic_trace step (List.get_mem steps position)
  have siteArgumentsExact :
      (sites.get site).formals.map
          (fun wire => (source.val.wires wire).sig) =
        receipt.inverse.args := by
    apply Sig.rel.inj
    calc
      .rel ((sites.get site).formals.map
          (fun wire => (source.val.wires wire).sig)) =
          (receipt.result.checked.val.wires
            receipt.result.relationWire).sig := by
        rw [receipt.result.site_formal_signatures site,
          receipt.result.relationWire_signature]
      _ = .rel receipt.inverse.args := receipt.inverse.relation_signature
  have arityExact :
      (sites.get site).formals.length = step.relationArgs.length := by
    calc
      (sites.get site).formals.length =
          ((sites.get site).formals.map
            (fun wire => (source.val.wires wire).sig)).length := by simp
      _ = receipt.inverse.args.length :=
        congrArg List.length siteArgumentsExact
      _ = step.relationArgs.length :=
        congrArg List.length stepExact.1.symm
  exact inverseStepOccurrenceAlignmentOfChecked receipt.result
    receipt.extractions.first content
    (receipt.extractions.entries.get contentPosition)
    receipt.parameters receipt.parametersAccepted step site siteExact
      applicationExact arityExact stepExact.2

/-- No step in an accepted inverse reconstruction can allocate an identity:
its complete boundary vector is the positional sever image of the original
checked occurrence. -/
theorem RelationSeverConcreteReceipt.inverseStep_identityRequestsEmpty
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (position : Fin receipt.inverse.steps.length) :
    (receipt.inverse.steps.get position).attachment.identityRequests = [] :=
  (receipt.inverseStepAlignment position).identityRequestsEmpty

/-- Snoc carrier step: transport the existing reconstructed prefix through
atom deletion and splice, then allocate the newly restored occurrence in the
fragment suffix.  The sole separation premise says that no original carrier
already represented by the prefix is the generated atom being consumed. -/
noncomputable def batchReconstructionSnoc
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {restored : List (ContentOccurrence source pattern)}
    {current : CheckedDiagram definitions}
    {joinSource : CheckedDiagram definitions}
    (state : BatchReconstructionState sites restored current joinSource)
    (content : ContentOccurrence source pattern)
    {dying : joinSource.val.WireId}
    (step : ConcreteWireQuantifier.RelationJoinStep joinSource dying pattern)
    (priorExact : step.prior = current)
    (priorNodeImageExact :
      HEq step.priorNodeImage state.joinNodeImage)
    (tail : List joinSource.val.NodeId)
    (pendingOriginsExact :
      state.pendingOrigins = step.application :: tail)
    (freshRegionsNew :
      ∀ region, region ≠ pattern.val.diagram.root →
        ¬ BatchCoveredRegion sites restored
          (content.occurrence.regionMap region))
    (freshNodesNew :
      ∀ node, ¬ BatchCoveredNode sites restored
        (content.occurrence.nodeMap node))
    (freshWiresNew :
      ∀ wire, wire ∉ pattern.val.boundary →
        ¬ BatchCoveredWire sites restored
          (content.occurrence.wireMap wire))
    (boundaryRetained :
      ∀ position : Fin pattern.val.boundary.length,
        retainedBySitesWire sites
          (content.occurrence.wireMap
            (pattern.val.boundary.get position)))
    (boundaryWireExact :
      ∀ position : Fin pattern.val.boundary.length,
        step.checkedFragmentWire (pattern.val.boundary.get position) =
          step.checkedPriorWire
            (Fin.cast
              (congrArg
                (fun checked : CheckedDiagram definitions =>
                  checked.val.wireCount) priorExact).symm
              (state.wireImage
                ⟨content.occurrence.wireMap
                    (pattern.val.boundary.get position),
                  Or.inl (boundaryRetained position)⟩)))
    (rootCovered :
      BatchCoveredRegion sites restored
        (content.occurrence.regionMap pattern.val.diagram.root))
    (rootExact :
      step.checkedFragmentRegion pattern.val.diagram.root =
        step.checkedPriorRegion
          (Fin.cast
            (congrArg
              (fun checked : CheckedDiagram definitions =>
                checked.val.regionCount) priorExact).symm
            (state.regionImage
              ⟨content.occurrence.regionMap pattern.val.diagram.root,
                rootCovered⟩))) :
    BatchReconstructionState sites (restored ++ [content]) step.checked
      joinSource := by
  classical
  subst current
  have priorNodeImageExact' :
      step.priorNodeImage = state.joinNodeImage :=
    eq_of_heq priorNodeImageExact
  have currentApplication :
      step.priorApplication ∈ state.pendingApplications := by
    rw [state.pendingApplicationsExact, pendingOriginsExact,
      ← priorNodeImageExact']
    simp only [List.filterMap_cons, step.priorApplicationImage,
      List.mem_cons, true_or]
  have coveredRegion_mono :
      ∀ {region}, BatchCoveredRegion sites restored region →
        BatchCoveredRegion sites (restored ++ [content]) region := by
    intro region covered
    rcases covered with retained | represented
    · exact Or.inl retained
    · rcases represented with
        ⟨candidate, member, patternRegion, nonroot, mapped⟩
      exact Or.inr
        ⟨candidate, List.mem_append.mpr (Or.inl member), patternRegion,
          nonroot, mapped⟩
  exact
    { regionImage := fun region =>
        if old : BatchCoveredRegion sites restored region.1 then
          step.checkedPriorRegion (state.regionImage ⟨region.1, old⟩)
        else
          have fresh := newlyCoveredRegion content region.1 region.2 old
          step.checkedFragmentRegion fresh.choose
      regionImage_injective := by
        intro left right same
        by_cases leftOld : BatchCoveredRegion sites restored left.1
        · by_cases rightOld : BatchCoveredRegion sites restored right.1
          · have priorSame :
                state.regionImage ⟨left.1, leftOld⟩ =
                  state.regionImage ⟨right.1, rightOld⟩ :=
              step.checkedPriorRegion_injective (by
                simpa only [dif_pos leftOld, dif_pos rightOld] using same)
            have coveredSame := state.regionImage_injective priorSame
            apply Subtype.ext
            exact congrArg
              (fun value : { region : source.val.RegionId //
                BatchCoveredRegion sites restored region } => value.1)
              coveredSame
          · let fresh := newlyCoveredRegion content right.1 right.2 rightOld
            exact False.elim
              (step.checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
                fresh.choose fresh.choose_spec.1
                (state.regionImage ⟨left.1, leftOld⟩) (by
                  simpa only [dif_pos leftOld, dif_neg rightOld] using
                    same.symm))
        · by_cases rightOld : BatchCoveredRegion sites restored right.1
          · let fresh := newlyCoveredRegion content left.1 left.2 leftOld
            exact False.elim
              (step.checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
                fresh.choose fresh.choose_spec.1
                (state.regionImage ⟨right.1, rightOld⟩) (by
                  simpa only [dif_neg leftOld, dif_pos rightOld] using same))
          · let leftFresh :=
                newlyCoveredRegion content left.1 left.2 leftOld
            let rightFresh :=
                newlyCoveredRegion content right.1 right.2 rightOld
            have patternSame : leftFresh.choose = rightFresh.choose :=
              step.checkedFragmentRegion_injective_of_nonroot
                leftFresh.choose_spec.1 rightFresh.choose_spec.1 (by
                  simpa only [dif_neg leftOld, dif_neg rightOld] using same)
            apply Subtype.ext
            exact leftFresh.choose_spec.2.symm.trans
              (patternSame ▸ rightFresh.choose_spec.2)
      retainedRegionImage_val := by
        intro region retained
        split
        next old =>
          rw [step.checkedPriorRegion_val]
          exact state.retainedRegionImage_val region retained
        next old => exact False.elim (old (Or.inl retained))
      regionParentCovered := by
        intro region parent data
        by_cases old : BatchCoveredRegion sites restored region.1
        · exact coveredRegion_mono
            (state.regionParentCovered ⟨region.1, old⟩ parent data)
        · let fresh := newlyCoveredRegion content region.1 region.2 old
          cases patternData : pattern.val.diagram.regions fresh.choose with
          | sheet =>
              have onlyRoot := of_decide_eq_true
                (List.all_eq_true.mp
                  pattern.property.diagram.only_root_is_sheet fresh.choose
                  (Data.Finite.mem_allFin fresh.choose))
              exact False.elim
                (fresh.choose_spec.1 (onlyRoot patternData))
          | cut patternParent =>
              have mappedData := content.occurrence.maps_parentage
                fresh.choose patternParent patternData
              rw [fresh.choose_spec.2] at mappedData
              have parentExact :
                  content.occurrence.regionMap patternParent = parent :=
                CRegion.cut.inj (mappedData.symm.trans data)
              subst parent
              by_cases parentRoot :
                  patternParent = pattern.val.diagram.root
              · subst patternParent
                exact coveredRegion_mono rootCovered
              · exact Or.inr
                  ⟨content, by simp, patternParent, parentRoot, rfl⟩
      regionSheetExact := by
        intro region data
        by_cases old : BatchCoveredRegion sites restored region.1
        · rw [dif_pos old]
          apply step.checkedPriorRegion_sheet
          exact state.regionSheetExact ⟨region.1, old⟩ data
        · let fresh := newlyCoveredRegion content region.1 region.2 old
          cases patternData : pattern.val.diagram.regions fresh.choose with
          | sheet =>
              have onlyRoot := of_decide_eq_true
                (List.all_eq_true.mp
                  pattern.property.diagram.only_root_is_sheet fresh.choose
                  (Data.Finite.mem_allFin fresh.choose))
              exact False.elim
                (fresh.choose_spec.1 (onlyRoot patternData))
          | cut patternParent =>
              have mappedData := content.occurrence.maps_parentage
                fresh.choose patternParent patternData
              rw [fresh.choose_spec.2, data] at mappedData
              contradiction
      regionCutExact := by
        intro region parent data
        by_cases old : BatchCoveredRegion sites restored region.1
        · have parentOld := state.regionParentCovered
            ⟨region.1, old⟩ parent data
          rw [dif_pos old, dif_pos parentOld]
          apply step.checkedPriorRegion_cut
          exact state.regionCutExact ⟨region.1, old⟩ parent data
        · let fresh := newlyCoveredRegion content region.1 region.2 old
          cases patternData : pattern.val.diagram.regions fresh.choose with
          | sheet =>
              have onlyRoot := of_decide_eq_true
                (List.all_eq_true.mp
                  pattern.property.diagram.only_root_is_sheet fresh.choose
                  (Data.Finite.mem_allFin fresh.choose))
              exact False.elim
                (fresh.choose_spec.1 (onlyRoot patternData))
          | cut patternParent =>
              have mappedData := content.occurrence.maps_parentage
                fresh.choose patternParent patternData
              rw [fresh.choose_spec.2] at mappedData
              have parentExact :
                  content.occurrence.regionMap patternParent = parent :=
                CRegion.cut.inj (mappedData.symm.trans data)
              subst parent
              rw [dif_neg old]
              rw [step.checkedFragmentRegion_cut fresh.choose patternParent
                fresh.choose_spec.1 patternData]
              by_cases parentRoot :
                  patternParent = pattern.val.diagram.root
              · subst patternParent
                rw [dif_pos rootCovered]
                exact congrArg CRegion.cut rootExact
              · have parentNew := freshRegionsNew patternParent parentRoot
                rw [dif_neg parentNew]
                let parentFresh := newlyCoveredRegion content
                  (content.occurrence.regionMap patternParent)
                  (Or.inr ⟨content, by simp, patternParent, parentRoot, rfl⟩)
                  parentNew
                have parentPatternExact :
                    parentFresh.choose = patternParent :=
                  content.occurrence.regionMap_injective
                    parentFresh.choose_spec.2
                exact congrArg
                  (fun candidate =>
                    CRegion.cut (step.checkedFragmentRegion candidate))
                  parentPatternExact.symm
      nodeImage := fun node =>
        if old : BatchCoveredNode sites restored node.1 then
          step.checkedPriorNode (state.nodeImage ⟨node.1, old⟩)
            (by
              intro same
              exact state.representedNodesAvoidPending ⟨node.1, old⟩
                (by simpa [same] using currentApplication))
        else
          have fresh := newlyCoveredNode content node.1 node.2 old
          step.checkedFragmentNode fresh.choose
      nodeImage_injective := by
        intro left right same
        by_cases leftOld : BatchCoveredNode sites restored left.1
        · by_cases rightOld : BatchCoveredNode sites restored right.1
          · have leftDifferent :
                state.nodeImage ⟨left.1, leftOld⟩ ≠
                  step.priorApplication := by
              intro exact
              exact state.representedNodesAvoidPending ⟨left.1, leftOld⟩
                (by simpa [exact] using currentApplication)
            have rightDifferent :
                state.nodeImage ⟨right.1, rightOld⟩ ≠
                  step.priorApplication := by
              intro exact
              exact state.representedNodesAvoidPending ⟨right.1, rightOld⟩
                (by simpa [exact] using currentApplication)
            have priorSame := step.checkedPriorNode_injective
              leftDifferent rightDifferent (by
                simpa only [dif_pos leftOld, dif_pos rightOld] using same)
            have coveredSame := state.nodeImage_injective priorSame
            apply Subtype.ext
            exact congrArg
              (fun value : { node : source.val.NodeId //
                BatchCoveredNode sites restored node } => value.1)
              coveredSame
          · let fresh := newlyCoveredNode content right.1 right.2 rightOld
            have leftDifferent :
                state.nodeImage ⟨left.1, leftOld⟩ ≠
                  step.priorApplication := by
              intro exact
              exact state.representedNodesAvoidPending ⟨left.1, leftOld⟩
                (by simpa [exact] using currentApplication)
            exact False.elim
              (step.checkedFragmentNode_ne_checkedPriorNode fresh.choose
                (state.nodeImage ⟨left.1, leftOld⟩) leftDifferent (by
                  simpa only [dif_pos leftOld, dif_neg rightOld] using
                    same.symm))
        · by_cases rightOld : BatchCoveredNode sites restored right.1
          · let fresh := newlyCoveredNode content left.1 left.2 leftOld
            have rightDifferent :
                state.nodeImage ⟨right.1, rightOld⟩ ≠
                  step.priorApplication := by
              intro exact
              exact state.representedNodesAvoidPending ⟨right.1, rightOld⟩
                (by simpa [exact] using currentApplication)
            exact False.elim
              (step.checkedFragmentNode_ne_checkedPriorNode fresh.choose
                (state.nodeImage ⟨right.1, rightOld⟩) rightDifferent (by
                  simpa only [dif_neg leftOld, dif_pos rightOld] using same))
          · let leftFresh := newlyCoveredNode content left.1 left.2 leftOld
            let rightFresh := newlyCoveredNode content right.1 right.2 rightOld
            have patternSame : leftFresh.choose = rightFresh.choose :=
              step.checkedFragmentNode_injective (by
                simpa only [dif_neg leftOld, dif_neg rightOld] using same)
            apply Subtype.ext
            exact leftFresh.choose_spec.symm.trans
              (patternSame ▸ rightFresh.choose_spec)
      nodeRegionCovered := by
        intro node
        by_cases old : BatchCoveredNode sites restored node.1
        · exact coveredRegion_mono
            (state.nodeRegionCovered ⟨node.1, old⟩)
        · let fresh := newlyCoveredNode content node.1 node.2 old
          have sourceData := content.occurrence.node_data fresh.choose
          rw [fresh.choose_spec] at sourceData
          have sourceRegionExact := congrArg CNode.region sourceData
          simp only [CNode.region_relocate] at sourceRegionExact
          rw [sourceRegionExact]
          by_cases root :
              (pattern.val.diagram.nodes fresh.choose).region =
                pattern.val.diagram.root
          · rw [root]
            exact coveredRegion_mono rootCovered
          · exact Or.inr
              ⟨content, by simp,
                (pattern.val.diagram.nodes fresh.choose).region, root, rfl⟩
      nodeTableExact := by
        intro node
        by_cases old : BatchCoveredNode sites restored node.1
        · have different :
              state.nodeImage ⟨node.1, old⟩ ≠ step.priorApplication := by
            intro same
            exact state.representedNodesAvoidPending ⟨node.1, old⟩
              (by simpa [same] using currentApplication)
          have transported := step.checkedPriorNode_data
            (state.nodeImage ⟨node.1, old⟩) different
          have priorData := state.nodeTableExact ⟨node.1, old⟩
          rw [priorData] at transported
          have regionOld := state.nodeRegionCovered ⟨node.1, old⟩
          simpa only [dif_pos old, dif_pos regionOld,
            CNode.region_relocate, CNode.relocate_relocate] using transported
        · let fresh := newlyCoveredNode content node.1 node.2 old
          have sourceData := content.occurrence.node_data fresh.choose
          rw [fresh.choose_spec] at sourceData
          have sourceRegionExact := congrArg CNode.region sourceData
          simp only [CNode.region_relocate] at sourceRegionExact
          have fragmentData := step.checkedFragmentNode_data fresh.choose
          simp only [dif_neg old]
          let allocatedRegion :
              { region : source.val.RegionId //
                BatchCoveredRegion sites (restored ++ [content]) region } →
                step.checked.val.RegionId := fun region =>
            if prior : BatchCoveredRegion sites restored region.1 then
              step.checkedPriorRegion (state.regionImage ⟨region.1, prior⟩)
            else
              have new := newlyCoveredRegion content region.1 region.2 prior
              step.checkedFragmentRegion new.choose
          have sourceCovered :
              BatchCoveredRegion sites (restored ++ [content])
                (source.val.nodes node.1).region := by
            have newData := content.occurrence.node_data fresh.choose
            rw [fresh.choose_spec] at newData
            have newRegion := congrArg CNode.region newData
            simp only [CNode.region_relocate] at newRegion
            rw [newRegion]
            by_cases atRoot :
                (pattern.val.diagram.nodes fresh.choose).region =
                  pattern.val.diagram.root
            · rw [atRoot]
              exact coveredRegion_mono rootCovered
            · exact Or.inr ⟨content, by simp,
                (pattern.val.diagram.nodes fresh.choose).region,
                atRoot, rfl⟩
          let sourceCarrier :
              { region : source.val.RegionId //
                BatchCoveredRegion sites (restored ++ [content]) region } :=
            ⟨(source.val.nodes node.1).region, sourceCovered⟩
          change step.checked.val.nodes
              (step.checkedFragmentNode fresh.choose) =
            (source.val.nodes node.1).relocate
              (allocatedRegion sourceCarrier)
          by_cases root :
              (pattern.val.diagram.nodes fresh.choose).region =
                pattern.val.diagram.root
          · have sourceRoot :
                (source.val.nodes node.1).region =
                  content.occurrence.regionMap pattern.val.diagram.root := by
              simpa [root] using sourceRegionExact
            have mappedImage :
                allocatedRegion
                    ⟨content.occurrence.regionMap pattern.val.diagram.root,
                      coveredRegion_mono rootCovered⟩ =
                  step.checkedFragmentRegion pattern.val.diagram.root := by
              unfold allocatedRegion
              rw [dif_pos rootCovered]
              exact rootExact.symm
            have sourceImage :
                allocatedRegion sourceCarrier =
                  step.checkedFragmentRegion pattern.val.diagram.root := by
              exact (congrArg allocatedRegion
                (Subtype.ext sourceRoot)).trans mappedImage
            have relocatedSource := congrArg
              (fun data => data.relocate (allocatedRegion sourceCarrier))
              sourceData
            calc
              step.checked.val.nodes
                    (step.checkedFragmentNode fresh.choose) =
                  (pattern.val.diagram.nodes fresh.choose).relocate
                    (step.checkedFragmentRegion
                      (pattern.val.diagram.nodes fresh.choose).region) :=
                fragmentData
              _ = (pattern.val.diagram.nodes fresh.choose).relocate
                    (step.checkedFragmentRegion pattern.val.diagram.root) := by
                rw [root]
              _ = (pattern.val.diagram.nodes fresh.choose).relocate
                    (allocatedRegion sourceCarrier) :=
                congrArg
                  (fun region =>
                    (pattern.val.diagram.nodes fresh.choose).relocate region)
                  sourceImage.symm
              _ = (source.val.nodes node.1).relocate
                    (allocatedRegion sourceCarrier) := by
                simpa only [CNode.relocate_relocate] using
                  relocatedSource.symm
          · have regionNew := freshRegionsNew
              (pattern.val.diagram.nodes fresh.choose).region root
            let regionFresh := newlyCoveredRegion content
              (content.occurrence.regionMap
                (pattern.val.diagram.nodes fresh.choose).region)
              (Or.inr ⟨content, by simp,
                (pattern.val.diagram.nodes fresh.choose).region, root, rfl⟩)
              regionNew
            have patternRegionExact :
                regionFresh.choose =
                  (pattern.val.diagram.nodes fresh.choose).region :=
              content.occurrence.regionMap_injective
                regionFresh.choose_spec.2
            have mappedImage :
                allocatedRegion
                    ⟨content.occurrence.regionMap
                        (pattern.val.diagram.nodes fresh.choose).region,
                      Or.inr ⟨content, by simp,
                        (pattern.val.diagram.nodes fresh.choose).region,
                        root, rfl⟩⟩ =
                  step.checkedFragmentRegion
                    (pattern.val.diagram.nodes fresh.choose).region := by
              unfold allocatedRegion
              rw [dif_neg regionNew]
              exact congrArg step.checkedFragmentRegion patternRegionExact
            have sourceImage :
                allocatedRegion sourceCarrier =
                  step.checkedFragmentRegion
                    (pattern.val.diagram.nodes fresh.choose).region := by
              exact (congrArg allocatedRegion
                (Subtype.ext sourceRegionExact)).trans mappedImage
            have relocatedSource := congrArg
              (fun data => data.relocate (allocatedRegion sourceCarrier))
              sourceData
            calc
              step.checked.val.nodes
                    (step.checkedFragmentNode fresh.choose) =
                  (pattern.val.diagram.nodes fresh.choose).relocate
                    (step.checkedFragmentRegion
                      (pattern.val.diagram.nodes fresh.choose).region) :=
                fragmentData
              _ = (pattern.val.diagram.nodes fresh.choose).relocate
                    (allocatedRegion sourceCarrier) :=
                congrArg
                  (fun region =>
                    (pattern.val.diagram.nodes fresh.choose).relocate region)
                  sourceImage.symm
              _ = (source.val.nodes node.1).relocate
                    (allocatedRegion sourceCarrier) := by
                simpa only [CNode.relocate_relocate] using
                  relocatedSource.symm
      portImage := fun node =>
        if old : BatchCoveredNode sites restored node.1 then
          state.portImage ⟨node.1, old⟩
        else
          have fresh := newlyCoveredNode content node.1 node.2 old
          (content.occurrence.portEquivForNode fresh.choose).symm
      portImageCorresponds := by
        intro node port required
        by_cases old : BatchCoveredNode sites restored node.1
        · have different :
              state.nodeImage ⟨node.1, old⟩ ≠ step.priorApplication := by
            intro same
            exact state.representedNodesAvoidPending ⟨node.1, old⟩
              (by simpa [same] using currentApplication)
          have transported := step.checkedPriorNode_data
            (state.nodeImage ⟨node.1, old⟩) different
          have priorData := state.nodeTableExact ⟨node.1, old⟩
          rw [priorData] at transported
          have priorCorresponds := state.portImageCorresponds
            ⟨node.1, old⟩ port required
          rw [dif_pos old]
          cases sourceData : source.val.nodes node.1 <;>
            simp_all [PortDataCorresponds, CNode.relocate]
        · let fresh := newlyCoveredNode content node.1 node.2 old
          simp only [dif_neg old]
          have sourceData := content.occurrence.node_data fresh.choose
          rw [fresh.choose_spec] at sourceData
          have fragmentData := step.checkedFragmentNode_data fresh.choose
          change PortDataCorresponds (source.val.nodes node.1)
            (step.checked.val.nodes
              (step.checkedFragmentNode fresh.choose)) port
            ((content.occurrence.portEquivForNode fresh.choose).symm port)
          cases patternData : pattern.val.diagram.nodes fresh.choose with
          | atom region args =>
              have portExact := content.occurrence.portEquivForNode_atom
                fresh.choose region args patternData
              rw [portExact]
              rw [sourceData, fragmentData, patternData]
              exact rfl
          | ref region definition args =>
              have portExact := content.occurrence.portEquivForNode_ref
                fresh.choose region definition args patternData
              rw [portExact]
              rw [sourceData, fragmentData, patternData]
              exact rfl
          | identity region sig arity =>
              have sourceNodeData : source.val.nodes node.1 =
                  .identity (content.occurrence.regionMap region) sig arity := by
                simpa [patternData, CNode.relocate] using sourceData
              have requiredIdentity :
                  port ∈ (List.range arity).map CPort.identity := by
                simpa [ConcreteDiagram.requiredPorts, sourceNodeData] using
                  required
              obtain ⟨index, indexMember, portExact⟩ :=
                List.mem_map.mp requiredIdentity
              have indexLt : index < arity := List.mem_range.mp indexMember
              subst port
              rw [content.occurrence.portEquivForNode_identity fresh.choose
                region sig arity patternData]
              rw [sourceNodeData, fragmentData, patternData]
              refine ⟨rfl, rfl, index,
                ((content.occurrence.identityPortEquiv fresh.choose region sig
                  arity patternData).symm ⟨index, indexLt⟩).1, rfl, ?_⟩
              simp [Occurrence.identityCPortEquiv, indexLt]
      portImageRequired := by
        intro node port
        by_cases old : BatchCoveredNode sites restored node.1
        · have different :
              state.nodeImage ⟨node.1, old⟩ ≠ step.priorApplication := by
            intro same
            exact state.representedNodesAvoidPending ⟨node.1, old⟩
              (by simpa [same] using currentApplication)
          have transported := step.checkedPriorNode_data
            (state.nodeImage ⟨node.1, old⟩) different
          have priorData := state.nodeTableExact ⟨node.1, old⟩
          have priorRequired := state.portImageRequired ⟨node.1, old⟩ port
          simp only [dif_pos old]
          rw [priorData] at transported
          rw [priorData] at priorRequired
          rw [transported]
          simpa using priorRequired
        · let fresh := newlyCoveredNode content node.1 node.2 old
          simp only [dif_neg old]
          have sourceData := content.occurrence.node_data fresh.choose
          rw [fresh.choose_spec] at sourceData
          have fragmentData := step.checkedFragmentNode_data fresh.choose
          cases patternData : pattern.val.diagram.nodes fresh.choose with
          | atom region args =>
              rw [content.occurrence.portEquivForNode_atom fresh.choose
                region args patternData]
              rw [sourceData, fragmentData, patternData]
              rfl
          | ref region definition args =>
              rw [content.occurrence.portEquivForNode_ref fresh.choose
                region definition args patternData]
              rw [sourceData, fragmentData, patternData]
              rfl
          | identity region sig arity =>
              rw [content.occurrence.portEquivForNode_identity fresh.choose
                region sig arity patternData]
              rw [sourceData, fragmentData, patternData]
              cases port with
              | head => simp [requiredPortsForNode, CNode.relocate, CNode.region,
                  Occurrence.identityCPortEquiv]
              | arg index => simp [requiredPortsForNode, CNode.relocate, CNode.region,
                  Occurrence.identityCPortEquiv]
              | identity index =>
                  by_cases indexLt : index < arity
                  · simp [requiredPortsForNode, CNode.relocate, CNode.region,
                      Occurrence.identityCPortEquiv, indexLt]
                  · simp [requiredPortsForNode, CNode.relocate, CNode.region,
                      Occurrence.identityCPortEquiv, indexLt]
      wireImage := fun wire =>
        if old : BatchCoveredWire sites restored wire.1 then
          step.checkedPriorWire (state.wireImage ⟨wire.1, old⟩)
        else
          have fresh := newlyCoveredWire content wire.1 wire.2 old
          step.checkedFragmentWire fresh.choose
      wireImage_injective := by
        intro left right same
        by_cases leftOld : BatchCoveredWire sites restored left.1
        · by_cases rightOld : BatchCoveredWire sites restored right.1
          · have priorSame :
                state.wireImage ⟨left.1, leftOld⟩ =
                  state.wireImage ⟨right.1, rightOld⟩ :=
              step.checkedPriorWire_injective (by
                simpa only [dif_pos leftOld, dif_pos rightOld] using same)
            have coveredSame := state.wireImage_injective priorSame
            apply Subtype.ext
            exact congrArg
              (fun value : { wire : source.val.WireId //
                BatchCoveredWire sites restored wire } => value.1)
              coveredSame
          · let fresh := newlyCoveredWire content right.1 right.2 rightOld
            exact False.elim
              (step.checkedFragmentWire_ne_checkedPriorWire_of_internal
                fresh.choose fresh.choose_spec.1
                (state.wireImage ⟨left.1, leftOld⟩) (by
                  simpa only [dif_pos leftOld, dif_neg rightOld] using
                    same.symm))
        · by_cases rightOld : BatchCoveredWire sites restored right.1
          · let fresh := newlyCoveredWire content left.1 left.2 leftOld
            exact False.elim
              (step.checkedFragmentWire_ne_checkedPriorWire_of_internal
                fresh.choose fresh.choose_spec.1
                (state.wireImage ⟨right.1, rightOld⟩) (by
                  simpa only [dif_neg leftOld, dif_pos rightOld] using same))
          · let leftFresh := newlyCoveredWire content left.1 left.2 leftOld
            let rightFresh := newlyCoveredWire content right.1 right.2 rightOld
            have patternSame : leftFresh.choose = rightFresh.choose :=
              step.checkedFragmentWire_injective_of_internal
                leftFresh.choose_spec.1 rightFresh.choose_spec.1 (by
                  simpa only [dif_neg leftOld, dif_neg rightOld] using same)
            apply Subtype.ext
            exact leftFresh.choose_spec.2.symm.trans
              (patternSame ▸ rightFresh.choose_spec.2)
      retainedWireImage_val := by
        intro wire retained
        have old : BatchCoveredWire sites restored wire := Or.inl retained
        rw [dif_pos old, step.checkedPriorWire_val]
        exact state.retainedWireImage_val wire retained
      wireScopeCovered := by
        intro wire
        by_cases old : BatchCoveredWire sites restored wire.1
        · exact coveredRegion_mono
            (state.wireScopeCovered ⟨wire.1, old⟩)
        · let fresh := newlyCoveredWire content wire.1 wire.2 old
          have scopeExact := content.occurrence.internalWire_scope
            fresh.choose fresh.choose_spec.1
          rw [fresh.choose_spec.2] at scopeExact
          rw [scopeExact]
          by_cases root :
              (pattern.val.diagram.wires fresh.choose).scope =
                pattern.val.diagram.root
          · rw [root]
            exact coveredRegion_mono rootCovered
          · exact Or.inr ⟨content, by simp,
              (pattern.val.diagram.wires fresh.choose).scope, root, rfl⟩
      wireSignatureExact := by
        intro wire
        by_cases old : BatchCoveredWire sites restored wire.1
        · rw [dif_pos old]
          calc
            (step.checked.val.wires
                (step.checkedPriorWire
                  (state.wireImage ⟨wire.1, old⟩))).sig =
                (step.prior.val.wires
                  (state.wireImage ⟨wire.1, old⟩)).sig :=
              step.checkedPriorWire_signature _
            _ = (source.val.wires wire.1).sig :=
              state.wireSignatureExact ⟨wire.1, old⟩
        · rw [dif_neg old]
          let fresh := newlyCoveredWire content wire.1 wire.2 old
          have sourceSignature := content.occurrence.wire_signature_preserved
            fresh.choose
          rw [fresh.choose_spec.2] at sourceSignature
          exact (step.checkedFragmentWire_signature_of_internal fresh.choose
            fresh.choose_spec.1).trans sourceSignature.symm
      wireScopeExact := by
        intro wire
        by_cases old : BatchCoveredWire sites restored wire.1
        · have transported := step.checkedPriorWire_scope
            (state.wireImage ⟨wire.1, old⟩)
          rw [state.wireScopeExact ⟨wire.1, old⟩] at transported
          have scopeOld := state.wireScopeCovered ⟨wire.1, old⟩
          simpa only [dif_pos old, dif_pos scopeOld] using transported
        · let fresh := newlyCoveredWire content wire.1 wire.2 old
          have sourceScope := content.occurrence.internalWire_scope
            fresh.choose fresh.choose_spec.1
          rw [fresh.choose_spec.2] at sourceScope
          have fragmentScope := step.checkedFragmentWire_scope_of_internal
            fresh.choose fresh.choose_spec.1
          rw [dif_neg old]
          let allocatedRegion :
              { region : source.val.RegionId //
                BatchCoveredRegion sites (restored ++ [content]) region } →
                step.checked.val.RegionId := fun region =>
            if prior : BatchCoveredRegion sites restored region.1 then
              step.checkedPriorRegion (state.regionImage ⟨region.1, prior⟩)
            else
              have new := newlyCoveredRegion content region.1 region.2 prior
              step.checkedFragmentRegion new.choose
          have sourceCovered :
              BatchCoveredRegion sites (restored ++ [content])
                (source.val.wires wire.1).scope := by
            rw [sourceScope]
            by_cases atRoot :
                (pattern.val.diagram.wires fresh.choose).scope =
                  pattern.val.diagram.root
            · rw [atRoot]
              exact coveredRegion_mono rootCovered
            · exact Or.inr ⟨content, by simp,
                (pattern.val.diagram.wires fresh.choose).scope,
                atRoot, rfl⟩
          let sourceCarrier :
              { region : source.val.RegionId //
                BatchCoveredRegion sites (restored ++ [content]) region } :=
            ⟨(source.val.wires wire.1).scope, sourceCovered⟩
          change
            (step.checked.val.wires
              (step.checkedFragmentWire fresh.choose)).scope =
                allocatedRegion sourceCarrier
          by_cases root :
              (pattern.val.diagram.wires fresh.choose).scope =
                pattern.val.diagram.root
          · have mappedImage :
                allocatedRegion
                    ⟨content.occurrence.regionMap pattern.val.diagram.root,
                      coveredRegion_mono rootCovered⟩ =
                  step.checkedFragmentRegion pattern.val.diagram.root := by
              unfold allocatedRegion
              rw [dif_pos rootCovered]
              exact rootExact.symm
            have sourceRoot :
                (source.val.wires wire.1).scope =
                  content.occurrence.regionMap pattern.val.diagram.root := by
              simpa [root] using sourceScope
            have sourceImage :
                allocatedRegion sourceCarrier =
                  step.checkedFragmentRegion pattern.val.diagram.root :=
              (congrArg allocatedRegion
                (Subtype.ext sourceRoot)).trans mappedImage
            rw [fragmentScope, root]
            exact sourceImage.symm
          · have regionNew := freshRegionsNew
              (pattern.val.diagram.wires fresh.choose).scope root
            let regionFresh := newlyCoveredRegion content
              (content.occurrence.regionMap
                (pattern.val.diagram.wires fresh.choose).scope)
              (Or.inr ⟨content, by simp,
                (pattern.val.diagram.wires fresh.choose).scope, root, rfl⟩)
              regionNew
            have patternRegionExact : regionFresh.choose =
                (pattern.val.diagram.wires fresh.choose).scope :=
              content.occurrence.regionMap_injective
                regionFresh.choose_spec.2
            have mappedImage :
                allocatedRegion
                    ⟨content.occurrence.regionMap
                        (pattern.val.diagram.wires fresh.choose).scope,
                      Or.inr ⟨content, by simp,
                        (pattern.val.diagram.wires fresh.choose).scope,
                        root, rfl⟩⟩ =
                  step.checkedFragmentRegion
                    (pattern.val.diagram.wires fresh.choose).scope := by
              unfold allocatedRegion
              rw [dif_neg regionNew]
              exact congrArg step.checkedFragmentRegion patternRegionExact
            have sourceImage :
                allocatedRegion sourceCarrier =
                  step.checkedFragmentRegion
                    (pattern.val.diagram.wires fresh.choose).scope :=
              (congrArg allocatedRegion
                (Subtype.ext sourceScope)).trans mappedImage
            exact fragmentScope.trans sourceImage.symm
      wireEndpointForward := by
        intro wire endpoint incident nodeCovered
        by_cases wireOld : BatchCoveredWire sites restored wire.1
        · by_cases nodeOld : BatchCoveredNode sites restored endpoint.node
          · let priorEndpoint : CEndpoint step.prior.val.nodeCount :=
              { node := state.nodeImage ⟨endpoint.node, nodeOld⟩
                port := state.portImage ⟨endpoint.node, nodeOld⟩ endpoint.port }
            have priorIncident := state.wireEndpointForward
              ⟨wire.1, wireOld⟩ endpoint incident nodeOld
            have different : priorEndpoint.node ≠ step.priorApplication := by
              intro same
              exact state.representedNodesAvoidPending ⟨endpoint.node, nodeOld⟩
                (by
                  have imageExact :
                      state.nodeImage ⟨endpoint.node, nodeOld⟩ =
                        step.priorApplication := by
                    simpa [priorEndpoint] using same
                  rw [imageExact]
                  exact currentApplication)
            have transported := step.checkedPriorEndpoint_mem
              (state.wireImage ⟨wire.1, wireOld⟩) priorEndpoint different
              priorIncident
            simpa only [dif_pos wireOld, dif_pos nodeOld,
              ConcreteWireQuantifier.RelationJoinStep.checkedPriorEndpoint,
              priorEndpoint] using transported
          · let freshNode := newlyCoveredNode content endpoint.node
              nodeCovered nodeOld
            rcases Reconstruction.occurrenceEndpointMap_preimage
                content.occurrence
                freshNode.choose wire.1 endpoint incident
                freshNode.choose_spec with
              ⟨patternWire, patternEndpoint, patternIncident,
                mappedWire, endpointExact⟩
            have patternNodeExact : patternEndpoint.node = freshNode.choose := by
              apply content.occurrence.nodeMap_injective
              exact (congrArg CEndpoint.node endpointExact).trans
                freshNode.choose_spec.symm
            have boundary : patternWire ∈ pattern.val.boundary :=
              Classical.byContradiction (fun internal =>
                (freshWiresNew patternWire internal)
                  (mappedWire ▸ wireOld))
            obtain ⟨position, positionExact⟩ := List.get_of_mem boundary
            have imageWireExact :
                step.checkedFragmentWire patternWire =
                  step.checkedPriorWire
                    (state.wireImage ⟨wire.1, wireOld⟩) := by
              subst patternWire
              rw [boundaryWireExact position]
              have carriers :
                  (⟨content.occurrence.wireMap
                      (pattern.val.boundary.get position),
                    Or.inl (boundaryRetained position)⟩ :
                    { sourceWire : source.val.WireId //
                      BatchCoveredWire sites restored sourceWire }) =
                    ⟨wire.1, wireOld⟩ := by
                apply Subtype.ext
                exact mappedWire
              apply congrArg step.checkedPriorWire
              apply Fin.ext
              simpa using congrArg Fin.val (congrArg state.wireImage carriers)
            have mappedIncident := step.checkedFragmentEndpoint_mem
              patternWire patternEndpoint patternIncident
            rw [imageWireExact] at mappedIncident
            have inversePortExact :
                (content.occurrence.portEquivForNode freshNode.choose).symm
                    endpoint.port = patternEndpoint.port := by
              rw [← congrArg CEndpoint.port endpointExact,
                ← patternNodeExact]
              exact Data.Finite.FiniteEquiv.symm_apply_apply _ _
            simpa only [dif_pos wireOld, dif_neg nodeOld,
              ConcreteWireQuantifier.RelationJoinStep.checkedFragmentEndpoint,
              Occurrence.endpointMapForNode, patternNodeExact,
              inversePortExact] using mappedIncident
        · let freshWire := newlyCoveredWire content wire.1 wire.2 wireOld
          by_cases nodeOld : BatchCoveredNode sites restored endpoint.node
          · have internalIncident : endpoint ∈
                (source.val.wires
                  (content.occurrence.wireMap freshWire.choose)).endpoints := by
              simpa [freshWire.choose_spec.2] using incident
            rcases Reconstruction.occurrenceInternalEndpoint_node_preimage
                content.occurrence
                freshWire.choose freshWire.choose_spec.1 endpoint
                internalIncident with
              ⟨patternEndpoint, _patternIncident, mappedNode⟩
            exact False.elim
              ((freshNodesNew patternEndpoint.node)
                (mappedNode ▸ nodeOld))
          · let freshNode := newlyCoveredNode content endpoint.node
              nodeCovered nodeOld
            rcases Reconstruction.occurrenceEndpointMap_preimage
                content.occurrence
                freshNode.choose wire.1 endpoint incident
                freshNode.choose_spec with
              ⟨patternWire, patternEndpoint, patternIncident,
                mappedWire, endpointExact⟩
            have patternInternal : patternWire ∉ pattern.val.boundary := by
              intro boundary
              exact content.occurrence.internalBoundary_disjoint
                freshWire.choose patternWire freshWire.choose_spec.1 boundary
                (freshWire.choose_spec.2.trans mappedWire.symm)
            have patternWireExact : patternWire = freshWire.choose :=
              content.occurrence.internalWire_injective
                patternWire freshWire.choose patternInternal
                freshWire.choose_spec.1
                (mappedWire.trans freshWire.choose_spec.2.symm)
            have patternNodeExact : patternEndpoint.node = freshNode.choose := by
              apply content.occurrence.nodeMap_injective
              exact (congrArg CEndpoint.node endpointExact).trans
                freshNode.choose_spec.symm
            have mappedIncident := step.checkedFragmentEndpoint_mem
              patternWire patternEndpoint patternIncident
            have inversePortExact :
                (content.occurrence.portEquivForNode freshNode.choose).symm
                    endpoint.port = patternEndpoint.port := by
              rw [← congrArg CEndpoint.port endpointExact,
                ← patternNodeExact]
              exact Data.Finite.FiniteEquiv.symm_apply_apply _ _
            simpa only [dif_neg wireOld, dif_neg nodeOld, patternWireExact,
              ConcreteWireQuantifier.RelationJoinStep.checkedFragmentEndpoint,
              Occurrence.endpointMapForNode, patternNodeExact,
              inversePortExact] using mappedIncident
      joinNodeImage := step.checkedNodeImage
      pendingOrigins := tail
      pendingApplications :=
        step.checkedRemainingNodes state.pendingApplications
      pendingApplicationsExact := by
        rw [state.pendingApplicationsExact, pendingOriginsExact,
          ← priorNodeImageExact', List.filterMap_cons,
          step.priorApplicationImage]
        change
          step.checkedRemainingNodes
              (step.priorApplication ::
                tail.filterMap step.priorNodeImage) =
            tail.filterMap step.checkedNodeImage
        rw [show
          step.checkedRemainingNodes
              (step.priorApplication ::
                tail.filterMap step.priorNodeImage) =
            step.checkedRemainingNodes
              (tail.filterMap step.priorNodeImage) by
          simp [ConcreteWireQuantifier.RelationJoinStep.checkedRemainingNodes]]
        exact
          (step.checkedNodeImages_eq_checkedRemainingNodes tail).symm
      representedNodesAvoidPending := by
        intro node pending
        unfold ConcreteWireQuantifier.RelationJoinStep.checkedRemainingNodes at pending
        rw [List.mem_filterMap] at pending
        rcases pending with ⟨prior, priorMember, emitted⟩
        split at emitted
        · rename_i priorDifferent
          have mapped := Option.some.inj emitted
          by_cases old : BatchCoveredNode sites restored node.1
          · have representedDifferent :
                state.nodeImage ⟨node.1, old⟩ ≠
                  step.priorApplication := by
              intro representedExact
              exact state.representedNodesAvoidPending ⟨node.1, old⟩
                (by simpa [representedExact] using currentApplication)
            have priorExact : state.nodeImage ⟨node.1, old⟩ = prior :=
              have mappedOld :
                  step.checkedPriorNode prior priorDifferent =
                    step.checkedPriorNode
                      (state.nodeImage ⟨node.1, old⟩)
                      representedDifferent := by
                simpa only [dif_pos old] using mapped
              step.checkedPriorNode_injective representedDifferent
                priorDifferent mappedOld.symm
            exact state.representedNodesAvoidPending ⟨node.1, old⟩
              (priorExact.symm ▸ priorMember)
          · have fresh : ∃ patternNode,
                content.occurrence.nodeMap patternNode = node.1 := by
              rcases node.2 with retained | restoredAll
              · exact False.elim (old (Or.inl retained))
              · rcases restoredAll with
                  ⟨candidate, member, patternNode, occurrenceExact⟩
                rcases List.mem_append.mp member with previous | final
                · exact False.elim
                    (old (Or.inr
                      ⟨candidate, previous, patternNode,
                        occurrenceExact⟩))
                · have candidateExact : candidate = content := by
                    simpa using final
                  subst candidate
                  exact ⟨patternNode, occurrenceExact⟩
            have mappedFresh :
                step.checkedPriorNode prior priorDifferent =
                  step.checkedFragmentNode fresh.choose := by
              simpa only [dif_neg old] using mapped
            exact step.checkedFragmentNode_ne_checkedPriorNode
              fresh.choose prior priorDifferent mappedFresh.symm
        · contradiction }


end Internal

end MonolithicWireQuantifier

end VisualProof
