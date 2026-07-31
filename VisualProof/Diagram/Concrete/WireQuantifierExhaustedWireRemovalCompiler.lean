import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalCorrespondence
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame
import VisualProof.Diagram.ContextZipper

namespace VisualProof

universe u v w

namespace ConcreteWireQuantifier

namespace ExhaustedWireRemovalSemantics

open Internal

/--
Close one retained ancestor binder block around a strict-above zipper. The
dying scope is excluded explicitly, so this constructor never crosses the
unequal local binder blocks that deletion changes.
-/
private def transportRenaming
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (rho : WireRenaming source' target') :
    WireRenaming source target :=
  fun {_} value => targetExact.symm ▸ rho (sourceExact ▸ value)

private theorem transportRenaming_reindexed_identity
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (rawTargetToSource : target' = source')
    (targetToSource : target = source)
    (rho : WireRenaming source' target')
    (rawIdentity :
      (fun {sig} (value : Var source' sig) =>
        rawTargetToSource ▸ rho value) =
        (fun {_} (value : Var source' _) => value)) :
    (fun {sig} (value : Var source sig) =>
      targetToSource ▸
        transportRenaming sourceExact targetExact rho value) =
      (fun {_} (value : Var source _) => value) := by
  cases sourceExact
  cases targetExact
  have proofExact : targetToSource = rawTargetToSource :=
    Subsingleton.elim _ _
  rw [proofExact]
  exact rawIdentity

private theorem envComp_transportRenaming
    {source source' target target' : List Sig}
    (sourceExact : source' = source)
    (targetExact : target' = target)
    (rho : WireRenaming source' target') :
    (fun (pre : PreModel.{u}) (env : Env pre target) =>
      sourceExact ▸ Env.comp (targetExact.symm ▸ env) rho) =
      (fun (pre : PreModel.{u}) (env : Env pre target) =>
        Env.comp env
          (transportRenaming sourceExact.symm targetExact.symm rho)) := by
  cases sourceExact
  cases targetExact
  rfl

private theorem cast_trans
    {α : Sort v} {motive : α → Sort w}
    {left middle right : α}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (value : motive left) :
    middleRight ▸ (leftMiddle ▸ value) =
      (leftMiddle.trans middleRight) ▸ value := by
  cases leftMiddle
  cases middleRight
  rfl

private theorem bindMany_reindexBound
    {leftBound rightBound outer hole : List Sig}
    (same : leftBound = rightBound)
    (inner :
      DiagramContext definitions hole (leftBound ++ outer)) :
    DiagramContext.bindMany leftBound inner =
      DiagramContext.bindMany rightBound
        ((congrArg (fun bound => bound ++ outer) same) ▸ inner) := by
  cases same
  rfl

noncomputable def retainedBindContextComposable
    {source : CheckedDiagram definitions}
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    (region : source.val.RegionId)
    (notScope : region ≠ (source.val.wires removed).scope)
    (above :
      ConcreteElaboration.ContextAbove source.val sourceContext region)
    (sourceInner :
      DiagramContext definitions sourceHole
        (sourceContext.extend region).sigs)
    (targetInner :
      DiagramContext definitions targetHole
        (targetContext.extend
          (targetRegion source removed region)).sigs)
    (holeMap : ∀ pre : PreModel.{u},
      Env pre targetHole → Env pre sourceHole)
    (inner :
      DiagramContext.ComposableSemanticZipper sourceInner targetInner
        (fun _pre env =>
          Env.comp env
            (contextProjection source removed
              (targetContext.extend (targetRegion source removed region))
              (sourceContext.extend region)
              (extend_contexts_correspond source removed correspond region)
              (removed_absent_extend source removed sourceContext region
                removedAbsent notScope)))
        holeMap) :
    DiagramContext.ComposableSemanticZipper
      (bindContextFor source.val sourceContext.ids
        (source.val.wiresAt region) sourceInner)
      (bindContextFor (Target source removed) targetContext.ids
        ((Target source removed).wiresAt
          (targetRegion source removed region)) targetInner)
      (fun _pre env =>
        Env.comp env
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
      holeMap := by
  let bound :=
    (source.val.wiresAt region).map
      (fun wire => (source.val.wires wire).sig)
  let outerRenaming :=
    (fun {_} value =>
      contextProjection source removed targetContext sourceContext correspond
        removedAbsent value :
      WireRenaming sourceContext.sigs targetContext.sigs)
  let fullRenaming :=
    (fun {_} value =>
      contextProjection source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        (removed_absent_extend source removed sourceContext region
          removedAbsent notScope) value :
      WireRenaming (sourceContext.extend region).sigs
        (targetContext.extend (targetRegion source removed region)).sigs)
  let sourceExact :
      (sourceContext.extend region).sigs =
        bound ++ sourceContext.sigs :=
    @List.map_append _ _
      (fun wire => (source.val.wires wire).sig)
      (source.val.wiresAt region) sourceContext.ids
  let targetExact :
      (targetContext.extend
          (targetRegion source removed region)).sigs =
        bound ++ targetContext.sigs :=
    (@List.map_append _ _
      (fun wire => ((Target source removed).wires wire).sig)
      ((Target source removed).wiresAt
        (targetRegion source removed region))
      targetContext.ids).trans
      (congrArg (fun localSigs => localSigs ++ targetContext.sigs)
        (retainedLocalSigs_eq source removed region notScope))
  let canonicalFullRenaming :
      WireRenaming (bound ++ sourceContext.sigs)
        (bound ++ targetContext.sigs) :=
    transportRenaming sourceExact.symm targetExact.symm fullRenaming
  let outerTargetToSource :=
    corresponding_sigs_eq source removed targetContext sourceContext
      correspond removedAbsent
  let fullTargetToSource :=
    corresponding_sigs_eq source removed
      (targetContext.extend (targetRegion source removed region))
      (sourceContext.extend region)
      (extend_contexts_correspond source removed correspond region)
      (removed_absent_extend source removed sourceContext region
        removedAbsent notScope)
  let canonicalTargetToSource :
      bound ++ targetContext.sigs = bound ++ sourceContext.sigs :=
    congrArg (List.append bound) outerTargetToSource
  have sourceExtendedNodup :
      (sourceContext.extend region).ids.Nodup :=
    ConcreteElaboration.extend_nodup definitions source.val source.property
      sourceContext region above
  have outerNodup : sourceContext.ids.Nodup := by
    have parts := sourceExtendedNodup
    rw [ConcreteElaboration.WireContext.extend,
      List.nodup_append] at parts
    exact parts.2.1
  have rawFullIdentity :
      (fun {sig} (value : Var (sourceContext.extend region).sigs sig) =>
        fullTargetToSource ▸ fullRenaming value) =
        (fun {_}
          (value : Var (sourceContext.extend region).sigs _) => value) :=
    by
      simpa only [fullTargetToSource, fullRenaming] using
        (contextProjection_reindexed_identity source removed
          (targetContext.extend (targetRegion source removed region))
          (sourceContext.extend region)
          (extend_contexts_correspond source removed correspond region)
          sourceExtendedNodup
          (removed_absent_extend source removed sourceContext region
            removedAbsent notScope))
  have outerIdentity :
      (fun {sig} (value : Var sourceContext.sigs sig) =>
        outerTargetToSource ▸ outerRenaming value) =
        (fun {_} (value : Var sourceContext.sigs _) => value) :=
    by
      simpa only [outerTargetToSource, outerRenaming] using
        (contextProjection_reindexed_identity source removed targetContext
          sourceContext correspond outerNodup removedAbsent)
  have canonicalFullIdentity :
      (fun {sig} (value : Var (bound ++ sourceContext.sigs) sig) =>
        canonicalTargetToSource ▸ canonicalFullRenaming value) =
        (fun {_}
          (value : Var (bound ++ sourceContext.sigs) _) => value) :=
    transportRenaming_reindexed_identity sourceExact.symm targetExact.symm
      fullTargetToSource canonicalTargetToSource fullRenaming
        rawFullIdentity
  have canonicalFullExact :
      (canonicalFullRenaming :
        WireRenaming (bound ++ sourceContext.sigs)
          (bound ++ targetContext.sigs)) =
        (DiagramContext.ComposableSemanticZipper.liftMany
          bound outerRenaming :
        WireRenaming (bound ++ sourceContext.sigs)
          (bound ++ targetContext.sigs)) :=
    by
      simpa only using
        (DiagramContext.ComposableSemanticZipper.eq_liftMany_of_reindexed_identity
          bound outerTargetToSource outerRenaming canonicalFullRenaming
            outerIdentity canonicalFullIdentity)
  have canonicalInnerRaw :=
    (inner.rebaseSourceOuter sourceExact).rebaseTargetOuter targetExact
  have canonicalInner :
      DiagramContext.ComposableSemanticZipper
        (sourceExact ▸ sourceInner) (targetExact ▸ targetInner)
        (fun (pre : PreModel.{u}) env =>
          Env.comp env canonicalFullRenaming)
        holeMap := by
    rw [← envComp_transportRenaming sourceExact targetExact fullRenaming]
    exact canonicalInnerRaw
  have liftedInner :
      DiagramContext.ComposableSemanticZipper
        (sourceExact ▸ sourceInner) (targetExact ▸ targetInner)
        (fun (pre : PreModel.{u}) env =>
          Env.comp env
            (DiagramContext.ComposableSemanticZipper.liftMany
              bound outerRenaming))
        holeMap := by
    rw [← canonicalFullExact]
    exact canonicalInner
  have boundComposable :=
    DiagramContext.ComposableSemanticZipper.bindMany
      bound outerRenaming liftedInner
  have sourceAncestorExact :
      bindContextFor source.val sourceContext.ids
          (source.val.wiresAt region) sourceInner =
        DiagramContext.bindMany bound (sourceExact ▸ sourceInner) := by
    rw [bindContextFor_eq_bindMany]
    unfold bound
    have proofExact :
        (@List.map_append _ _
            (fun wire => (source.val.wires wire).sig)
            (source.val.wiresAt region) sourceContext.ids) =
          sourceExact :=
      Subsingleton.elim _ _
    rw [proofExact]
    rfl
  have targetAncestorExact :
      bindContextFor (Target source removed) targetContext.ids
          ((Target source removed).wiresAt
            (targetRegion source removed region)) targetInner =
        DiagramContext.bindMany bound (targetExact ▸ targetInner) := by
    rw [bindContextFor_eq_bindMany]
    change
      DiagramContext.bindMany
          (((Target source removed).wiresAt
            (targetRegion source removed region)).map
              (fun wire => ((Target source removed).wires wire).sig))
          ((@List.map_append _ _
            (fun wire => ((Target source removed).wires wire).sig)
            ((Target source removed).wiresAt
              (targetRegion source removed region))
            targetContext.ids) ▸ targetInner) =
        DiagramContext.bindMany bound (targetExact ▸ targetInner)
    rw [bindMany_reindexBound
      (retainedLocalSigs_eq source removed region notScope)]
    apply congrArg (DiagramContext.bindMany bound)
    unfold bound
    let mapAppend :=
      @List.map_append _ _
        (fun wire => ((Target source removed).wires wire).sig)
        ((Target source removed).wiresAt
          (targetRegion source removed region))
        targetContext.ids
    let localExact :
        (((Target source removed).wiresAt
          (targetRegion source removed region)).map
            (fun wire => ((Target source removed).wires wire).sig)) ++
              targetContext.sigs =
          (source.val.wiresAt region).map
              (fun wire => (source.val.wires wire).sig) ++
                targetContext.sigs :=
      congrArg (fun localSigs => localSigs ++ targetContext.sigs)
        (retainedLocalSigs_eq source removed region notScope)
    calc
      _ = (mapAppend.trans localExact) ▸ targetInner := by
        exact cast_trans mapAppend localExact targetInner <;> rfl
      _ = targetExact ▸ targetInner := by
        have proofExact : mapAppend.trans localExact = targetExact :=
          Subsingleton.elim _ _
        rw [proofExact] <;> rfl
    all_goals rfl
  rw [sourceAncestorExact, targetAncestorExact]
  simpa only [outerRenaming] using boundComposable

private def targetEndpoint
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint (Target source removed).nodeCount :=
  ⟨targetNode source removed endpoint.node, endpoint.port⟩

private theorem targetEndpoint_incident
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : source.val.WireId)
    (survives : wire ≠ removed)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires wire).endpoints) :
    targetEndpoint source removed endpoint ∈
      ((Target source removed).wires
        (targetWire source removed wire survives)).endpoints := by
  unfold Target targetWire targetEndpoint targetNode retainedNodes
  simp only [
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate,
    DenseList.get_index]
  apply List.mem_filterMap.mpr
  refine ⟨endpoint, incident, ?_⟩
  split
  · rename_i retained
    congr 1
  · rename_i rejected
    exfalso
    apply rejected
    simp [ConcreteDiagram.nodesList, Data.Finite.mem_allFin]

theorem requiredPorts_sourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (node : (Target source removed).NodeId) :
    (Target source removed).requiredPorts node =
      source.val.requiredPorts (sourceNode source removed node) := by
  cases targetData : (Target source removed).nodes node <;>
    have shape := sourceNode_shape source removed node <;>
    simp only [targetData] at shape <;>
    simp [ConcreteDiagram.requiredPorts, targetData, shape]

private theorem required_owner_image
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    {targetContext :
      ConcreteElaboration.WireContext (Target source removed)}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (targetNodeId : (Target source removed).NodeId)
    (port : CPort)
    (sourceRequired :
      port ∈ source.val.requiredPorts
        (sourceNode source removed targetNodeId))
    (sourceOwnerWire : source.val.WireId)
    (sourceOwner : source.val.endpointOwner?
        ⟨sourceNode source removed targetNodeId, port⟩ =
      some sourceOwnerWire)
    (sourceMember : sourceOwnerWire ∈ sourceContext.ids) :
    ∃ targetWireId : (Target source removed).WireId,
      (Target source removed).endpointOwner?
          ⟨targetNodeId, port⟩ =
        some targetWireId ∧
      sourceWire source removed targetWireId = sourceOwnerWire ∧
      targetWireId ∈ targetContext.ids := by
  have sourceIncident :=
    ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode source removed targetNodeId, port⟩ sourceOwnerWire
      sourceOwner
  have survives : sourceOwnerWire ≠ removed := by
    intro same
    subst sourceOwnerWire
    rw [removedEndpoints] at sourceIncident
    simp at sourceIncident
  let targetWireId :=
    targetWire source removed sourceOwnerWire survives
  have targetIncident :
      (⟨targetNodeId, port⟩ :
        CEndpoint (Target source removed).nodeCount) ∈
        ((Target source removed).wires targetWireId).endpoints := by
    have mapped :=
      targetEndpoint_incident source removed sourceOwnerWire survives
        ⟨sourceNode source removed targetNodeId, port⟩ sourceIncident
    simpa [targetEndpoint, targetWireId] using mapped
  have targetRequired :
      port ∈ (Target source removed).requiredPorts targetNodeId := by
    rw [requiredPorts_sourceNode]
    exact sourceRequired
  have targetOwner :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions
      (Target source removed) targetWellFormed targetNodeId port
      targetRequired targetWireId targetIncident
  refine ⟨targetWireId, targetOwner, ?_, ?_⟩
  · exact sourceWire_targetWire source removed sourceOwnerWire survives
  · exact target_visible source removed correspond sourceOwnerWire survives
      sourceMember

private theorem compileNode_singleton_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (targetNodeId : (Target source removed).NodeId)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          [sourceNode source removed targetNodeId] =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      ConcreteElaboration.compileNodes? definitions
          (Target source removed) targetContext [targetNodeId] =
        some targetItems ∧
      sourceItems =
        targetItems.renameWires
          (contextEmbedding source removed targetContext sourceContext
            correspond) := by
  apply ConcreteElaboration.compileNodes?_singleton_reflect
    (target := Target source removed) (source := source.val)
    (targetContext := targetContext) (sourceContext := sourceContext)
    source.property sourceNodup
    (contextEmbedding source removed targetContext sourceContext correspond)
    (sourceWire source removed)
    (sourceWire_signature source removed)
    (contextEmbedding_action source removed targetContext sourceContext
      correspond)
    (sourceRegion source removed)
    targetNodeId (sourceNode source removed targetNodeId)
  · have copied :=
      targetNode_shape source removed
        (sourceNode source removed targetNodeId)
    rw [targetNode_sourceNode] at copied
    rw [copied]
    cases source.val.nodes
        (sourceNode source removed targetNodeId) <;> simp
  · intro port required sourceOwnerWire owner member
    exact required_owner_image source removed targetWellFormed
      removedEndpoints correspond targetNodeId port required
      sourceOwnerWire owner member
  · exact sourceCompiled

/-- Reflect an accepted ordered source node list without reordering it. -/
theorem compileNodes_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup) :
    ∀ (targetNodes : List (Target source removed).NodeId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          (targetNodes.map (sourceNode source removed)) =
        some sourceItems →
      ∃ targetItems : ItemSeq definitions targetContext.sigs,
        ConcreteElaboration.compileNodes? definitions
            (Target source removed) targetContext targetNodes =
          some targetItems ∧
        sourceItems =
          targetItems.renameWires
            (contextEmbedding source removed targetContext sourceContext
              correspond) := by
  intro targetNodes
  induction targetNodes with
  | nil =>
      intro sourceItems sourceCompiled
      have sourceEquality :
          (.nil : ItemSeq definitions sourceContext.sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using sourceCompiled)
      subst sourceItems
      exact ⟨.nil, rfl, rfl⟩
  | cons targetNodeId tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
          sourceTailCompiled, sourceItemsEquality⟩ :=
        InsertionCompilation.NaturalityInternal.compileNodes_cons_components
          definitions source.val sourceContext
          (sourceNode source removed targetNodeId)
          (tail.map (sourceNode source removed)) sourceItems
          (by simpa using sourceCompiled)
      obtain ⟨targetHead, targetHeadCompiled, sourceHeadEquality⟩ :=
        compileNode_singleton_reflect source removed targetWellFormed
          removedEndpoints targetContext sourceContext correspond
          sourceNodup targetNodeId sourceHeadCompiled
      obtain ⟨targetTail, targetTailCompiled, sourceTailEquality⟩ :=
        induction sourceTailCompiled
      simp only [ConcreteElaboration.compileNodes?] at targetHeadCompiled
      obtain ⟨targetItem, targetItemCompiled, targetHeadResult⟩ :=
        Option.bind_eq_some_iff.mp targetHeadCompiled
      have targetHeadEquality :
          (ItemSeq.cons targetItem .nil :
            ItemSeq definitions targetContext.sigs) =
            targetHead :=
        Option.some.inj targetHeadResult
      subst targetHead
      refine ⟨.cons targetItem targetTail, ?_, ?_⟩
      · simp only [ConcreteElaboration.compileNodes?]
        rw [targetItemCompiled, targetTailCompiled]
        rfl
      · cases sourceHeadEquality
        simp [sourceItemsEquality, sourceTailEquality,
          ItemSeq.renameWires]

/-- Reflect the exact stored node order at one copied region. -/
theorem compileRegionNodes_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (region : source.val.RegionId)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          (source.val.nodesAt region) =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      ConcreteElaboration.compileNodes? definitions
          (Target source removed) targetContext
          ((Target source removed).nodesAt
            (targetRegion source removed region)) =
        some targetItems ∧
      sourceItems =
        targetItems.renameWires
          (contextEmbedding source removed targetContext sourceContext
            correspond) := by
  apply compileNodes_reflect source removed targetWellFormed
    removedEndpoints targetContext sourceContext correspond sourceNodup
  rw [nodesAt_sources]
  exact sourceCompiled

theorem Internal.climb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) :
    diagram.climb (steps + 1) diagram.root = none := by
  have rootData : diagram.regions diagram.root = .sheet :=
    wellFormed.root_is_sheet
  simp [ConcreteDiagram.climb, rootData]

theorem Internal.climb_to_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          rw [climb_succ_root_none definitions diagram wellFormed right]
            at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          rw [climb_succ_root_none definitions diagram wellFormed left]
            at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet =>
              simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              apply congrArg Nat.succ
              apply induction
              · simpa [ConcreteDiagram.climb, regionData] using leftClimb
              · simpa [ConcreteDiagram.climb, regionData] using rightClimb

theorem Internal.checked_reaches_root
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    ∃ steps : Fin (source.val.regionCount + 1),
      source.val.climb steps region = some source.val.root := by
  have checked :=
    (List.all_eq_true.mp source.property.all_regions_reach_root)
      region (Data.Finite.mem_allFin region)
  exact
    (ConcreteElaboration.encloses_iff_exists
      source.val source.val.root region).mp (of_decide_eq_true checked)

theorem checked_encloses_trans
    (source : CheckedDiagram definitions)
    {outer middle inner : source.val.RegionId}
    (outerMiddle : source.val.Encloses outer middle)
    (middleInner : source.val.Encloses middle inner) :
    source.val.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val outer middle).mp outerMiddle
  obtain ⟨middleSteps, middleClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val middle inner).mp middleInner
  obtain ⟨rootSteps, outerRoot⟩ := checked_reaches_root source outer
  have composed :
      source.val.climb (middleSteps.val + outerSteps.val) inner =
        some outer := by
    rw [ConcreteDiagram.climb_add source.val middleSteps.val outerSteps.val inner,
      middleClimb]
    exact outerClimb
  have composedRoot :
      source.val.climb
          ((middleSteps.val + outerSteps.val) + rootSteps.val) inner =
        some source.val.root := by
    rw [ConcreteDiagram.climb_add source.val
      (middleSteps.val + outerSteps.val) rootSteps.val inner, composed]
    exact outerRoot
  obtain ⟨canonicalRootSteps, canonicalRoot⟩ :=
    checked_reaches_root source inner
  have sameDepth :=
    climb_to_root_unique definitions source.val source.property
      composedRoot canonicalRoot
  have composedBound :
      middleSteps.val + outerSteps.val < source.val.regionCount + 1 := by
    omega
  exact
    (ConcreteElaboration.encloses_iff_exists source.val outer inner).mpr
      ⟨⟨middleSteps.val + outerSteps.val, composedBound⟩, composed⟩

private theorem child_outside
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (region child : source.val.RegionId)
    (outside :
      ¬source.val.Encloses region (source.val.wires removed).scope)
    (member : child ∈ source.val.childrenOf region) :
    ¬source.val.Encloses child (source.val.wires removed).scope := by
  intro childSite
  have childData :=
    ConcreteElaboration.mem_childrenOf source.val region child member
  have parentChild :
      source.val.Encloses region child := by
    apply
      (ConcreteElaboration.encloses_iff_exists source.val region child).mpr
    refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
    simp [ConcreteDiagram.climb, childData]
  exact outside (checked_encloses_trans source parentChild childSite)

private theorem child_outside_parent
    (source : CheckedDiagram definitions)
    (region child : source.val.RegionId)
    (member : child ∈ source.val.childrenOf region) :
    ¬source.val.Encloses child region := by
  intro childRegion
  have childData :=
    ConcreteElaboration.mem_childrenOf source.val region child member
  obtain ⟨backSteps, backClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val child region).mp childRegion
  obtain ⟨rootSteps, rootClimb⟩ := checked_reaches_root source child
  have cycle :
      source.val.climb (1 + backSteps.val) child = some child := by
    rw [ConcreteDiagram.climb_add source.val 1 backSteps.val child]
    simp [ConcreteDiagram.climb, childData, backClimb]
  have longRoot :
      source.val.climb ((1 + backSteps.val) + rootSteps.val) child =
        some source.val.root := by
    rw [ConcreteDiagram.climb_add source.val (1 + backSteps.val) rootSteps.val child,
      cycle]
    exact rootClimb
  have sameLength :=
    climb_to_root_unique definitions source.val source.property
      longRoot rootClimb
  omega

/-- Complete retained region binders preserve the reflected core equivalence. -/
private theorem finishRetainedRegion_equiv
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    (region : source.val.RegionId)
    (outside :
      ¬source.val.Encloses region (source.val.wires removed).scope)
    (above :
      ConcreteElaboration.ContextAbove source.val sourceContext region)
    (targetBody :
      Region definitions
        (targetContext.extend
          (targetRegion source removed region)).sigs)
    (sourceBody :
      Region definitions (sourceContext.extend region).sigs)
    (coreEquiv :
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (targetEnv :
          Env pre
            (targetContext.extend
              (targetRegion source removed region)).sigs),
        denoteRegion pre definitionEnv targetEnv targetBody ↔
          denoteRegion pre definitionEnv
            (Env.comp targetEnv
              (contextProjection source removed
                (targetContext.extend
                  (targetRegion source removed region))
                (sourceContext.extend region)
                (extend_contexts_correspond source removed correspond region)
                (removed_absent_extend source removed sourceContext region
                  removedAbsent
                  (fun same => outside
                    (same ▸ source.val.encloses_refl region)))))
            sourceBody)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (targetOuter : Env pre targetContext.sigs) :
    denoteRegion pre definitionEnv targetOuter
        (ConcreteElaboration.finishRegion (Target source removed)
          targetContext (targetRegion source removed region) targetBody) ↔
      denoteRegion pre definitionEnv
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        (ConcreteElaboration.finishRegion source.val sourceContext region
          sourceBody) := by
  have notScope :
      region ≠ (source.val.wires removed).scope :=
    fun same => outside (same ▸ source.val.encloses_refl region)
  have sourceExtendedNodup :
      (sourceContext.extend region).ids.Nodup :=
    ConcreteElaboration.extend_nodup definitions source.val source.property
      sourceContext region above
  constructor
  · intro targetFinished
    obtain ⟨targetValues, targetCore⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions
        (Target source removed) targetContext
        (targetRegion source removed region) pre definitionEnv targetOuter
        targetBody).mp targetFinished
    obtain ⟨sourceValues, environments⟩ :=
      (extendedEnvironment_correspondence source removed targetContext
        sourceContext correspond region sourceExtendedNodup removedAbsent
        notScope pre
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        targetOuter rfl).2 targetValues
    apply
      (ConcreteElaboration.denote_finishRegion definitions source.val
        sourceContext region pre definitionEnv
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        sourceBody).mpr
    refine ⟨sourceValues, ?_⟩
    rw [environments]
    exact (coreEquiv pre definitionEnv _).mp targetCore
  · intro sourceFinished
    obtain ⟨sourceValues, sourceCore⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions source.val
        sourceContext region pre definitionEnv
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        sourceBody).mp sourceFinished
    obtain ⟨targetValues, environments⟩ :=
      (extendedEnvironment_correspondence source removed targetContext
        sourceContext correspond region sourceExtendedNodup removedAbsent
        notScope pre
        (Env.comp targetOuter
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        targetOuter rfl).1 sourceValues
    apply
      (ConcreteElaboration.denote_finishRegion definitions
        (Target source removed) targetContext
        (targetRegion source removed region) pre definitionEnv targetOuter
        targetBody).mpr
    refine ⟨targetValues, ?_⟩
    apply (coreEquiv pre definitionEnv _).mpr
    rw [← environments]
    exact sourceCore

theorem compileChildren_reflect_of
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
        Option (Region definitions context.sigs))
    (targetRecurse : (region : (Target source removed).RegionId) →
      (context :
        ConcreteElaboration.WireContext (Target source removed)) →
        Option (Region definitions context.sigs))
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext) :
    ∀ (targetChildren : List (Target source removed).RegionId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext
          (targetChildren.map (sourceRegion source removed)) =
        some sourceItems →
      (∀ targetChild, targetChild ∈ targetChildren →
        ∀ sourceBody,
          sourceRecurse (sourceRegion source removed targetChild)
              sourceContext =
            some sourceBody →
          ∃ targetBody,
            targetRecurse targetChild targetContext =
                some targetBody ∧
              ∀ (removedAbsent : removed ∉ sourceContext.ids)
                (_outside :
                  ¬source.val.Encloses
                    (sourceRegion source removed targetChild)
                    (source.val.wires removed).scope),
              ∀ (pre : PreModel.{u})
                (definitionEnv : DefinitionEnv pre definitions)
                (targetEnv : Env pre targetContext.sigs),
                denoteRegion pre definitionEnv targetEnv targetBody ↔
                  denoteRegion pre definitionEnv
                    (Env.comp targetEnv
                      (contextProjection source removed targetContext
                        sourceContext correspond removedAbsent))
                    sourceBody) →
      ∃ targetItems : ItemSeq definitions targetContext.sigs,
        ConcreteElaboration.compileChildrenWith? definitions
            (Target source removed) targetRecurse targetContext
            targetChildren =
            some targetItems ∧
          ∀ (removedAbsent : removed ∉ sourceContext.ids)
            (_eachOutside :
              ∀ targetChild, targetChild ∈ targetChildren →
                ¬source.val.Encloses
                  (sourceRegion source removed targetChild)
                  (source.val.wires removed).scope),
          ∀ (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (targetEnv : Env pre targetContext.sigs),
            denoteItemSeq pre definitionEnv targetEnv targetItems ↔
              denoteItemSeq pre definitionEnv
                (Env.comp targetEnv
                  (contextProjection source removed targetContext
                    sourceContext correspond removedAbsent))
                sourceItems := by
  intro targetChildren
  induction targetChildren with
  | nil =>
      intro sourceItems sourceCompiled each
      have sourceEmpty : sourceItems = .nil := by
        simpa [ConcreteElaboration.compileChildrenWith?] using
          Option.some.inj sourceCompiled.symm
      subst sourceItems
      exact ⟨.nil, by
        simp [ConcreteElaboration.compileChildrenWith?], by simp⟩
  | cons targetChild tail induction =>
      intro sourceItems sourceCompiled each
      obtain ⟨sourceBody, sourceRest, sourceBodyCompiled,
          sourceRestCompiled, sourceExact⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions source.val sourceRecurse sourceContext
          (sourceRegion source removed targetChild)
          (tail.map (sourceRegion source removed)) sourceItems
          (by simpa using sourceCompiled)
      subst sourceItems
      obtain ⟨targetBody, targetBodyCompiled, bodyLaw⟩ :=
        each targetChild (by simp) sourceBody sourceBodyCompiled
      obtain ⟨targetRest, targetRestCompiled, restLaw⟩ :=
        induction sourceRestCompiled (by
          intro candidate member body compiled
          exact each candidate (List.mem_cons_of_mem targetChild member)
            body compiled)
      refine ⟨.cons (.cut targetBody) targetRest, ?_, ?_⟩
      · simp [ConcreteElaboration.compileChildrenWith?,
          targetBodyCompiled, targetRestCompiled]
      · intro removedAbsent eachOutside pre definitionEnv targetEnv
        simp only [denoteItemSeq_cons, cut_denotes_negation]
        exact and_congr
          (not_congr
            (bodyLaw removedAbsent
              (eachOutside targetChild (by simp))
              pre definitionEnv targetEnv))
          (restLaw removedAbsent
            (fun candidate member =>
              eachOutside candidate
                (List.mem_cons_of_mem targetChild member))
            pre definitionEnv targetEnv)

/--
Pair exact source and target child compiler results under a caller-supplied
semantic law for each corresponding child body.
-/
private theorem compileChildren_corresponding_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
        Option (Region definitions context.sigs))
    (targetRecurse : (region : (Target source removed).RegionId) →
      (context :
        ConcreteElaboration.WireContext (Target source removed)) →
        Option (Region definitions context.sigs))
    (targetChildren : List (Target source removed).RegionId)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext
          (targetChildren.map (sourceRegion source removed)) =
        some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          (Target source removed) targetRecurse targetContext targetChildren =
        some targetItems)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (sourceEnv : Env pre sourceContext.sigs)
    (bodyLaw :
      ∀ targetChild, targetChild ∈ targetChildren →
        ∀ sourceBody targetBody,
          sourceRecurse (sourceRegion source removed targetChild)
              sourceContext =
            some sourceBody →
          targetRecurse targetChild targetContext =
            some targetBody →
          (denoteRegion pre definitionEnv targetEnv targetBody ↔
            denoteRegion pre definitionEnv sourceEnv sourceBody)) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv sourceEnv sourceItems := by
  induction targetChildren generalizing sourceItems targetItems with
  | nil =>
      simp only [List.map_nil,
        ConcreteElaboration.compileChildrenWith?] at sourceCompiled
      simp only [ConcreteElaboration.compileChildrenWith?] at targetCompiled
      have sourceEmpty : sourceItems = .nil :=
        Option.some.inj sourceCompiled.symm
      have targetEmpty : targetItems = .nil :=
        Option.some.inj targetCompiled.symm
      subst sourceItems
      subst targetItems
      exact Iff.rfl
  | cons targetChild tail induction =>
      obtain ⟨sourceBody, sourceRest, sourceBodyCompiled,
          sourceRestCompiled, sourceExact⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions source.val sourceRecurse sourceContext
          (sourceRegion source removed targetChild)
          (tail.map (sourceRegion source removed)) sourceItems
          (by simpa using sourceCompiled)
      obtain ⟨targetBody, targetRest, targetBodyCompiled,
          targetRestCompiled, targetExact⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions (Target source removed) targetRecurse targetContext
          targetChild tail targetItems targetCompiled
      subst sourceItems
      subst targetItems
      simp only [denoteItemSeq_cons, cut_denotes_negation]
      exact and_congr
        (not_congr
          (bodyLaw targetChild (by simp) sourceBody targetBody
            sourceBodyCompiled targetBodyCompiled))
        (induction sourceRest targetRest sourceRestCompiled
          targetRestCompiled (by
            intro candidate member sourceCandidate targetCandidate
              sourceCandidateCompiled targetCandidateCompiled
            exact
              bodyLaw candidate (List.mem_cons_of_mem targetChild member)
                sourceCandidate targetCandidate sourceCandidateCompiled
                targetCandidateCompiled))

/--
Exact fueled compilations of a retained region have equivalent denotation
under corresponding deletion environments.  This is the recursive child law
needed at the removed wire's own unbound body.
-/
private theorem compileRegion_corresponding_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = []) :
    ∀ (fuel : Nat)
      (targetContext :
        ConcreteElaboration.WireContext (Target source removed))
      (sourceContext : ConcreteElaboration.WireContext source.val)
      (correspond : ContextsCorrespond source removed
        targetContext sourceContext)
      (region : source.val.RegionId)
      (above :
        ConcreteElaboration.ContextAbove source.val sourceContext region)
      (outside :
        ¬source.val.Encloses region (source.val.wires removed).scope)
      (sourceBody : Region definitions sourceContext.sigs)
      (targetBody : Region definitions targetContext.sigs),
      ConcreteElaboration.compileRegion? definitions source.val fuel
          region sourceContext =
        some sourceBody →
      ConcreteElaboration.compileRegion? definitions (Target source removed)
          fuel (targetRegion source removed region) targetContext =
        some targetBody →
      ∀ (pre : PreModel.{u})
        (definitionEnv : DefinitionEnv pre definitions)
        (specified : pre.Domain (source.val.wires removed).sig)
        (targetEnv : Env pre targetContext.sigs)
        (sourceEnv : Env pre sourceContext.sigs),
        EnvironmentsCorrespond source removed targetContext sourceContext
            correspond pre specified targetEnv sourceEnv →
          (denoteRegion pre definitionEnv targetEnv targetBody ↔
            denoteRegion pre definitionEnv sourceEnv sourceBody) := by
  intro fuel
  induction fuel with
  | zero =>
      intro targetContext sourceContext correspond region above outside
        sourceBody targetBody sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel induction =>
      intro targetContext sourceContext correspond region above outside
        sourceBody targetBody sourceCompiled targetCompiled pre definitionEnv
        specified targetEnv sourceEnv environments
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled
      simp only [ConcreteElaboration.compileRegion?] at targetCompiled
      cases sourceNodesEquation :
          ConcreteElaboration.compileNodes? definitions source.val
            (sourceContext.extend region) (source.val.nodesAt region) with
      | none =>
          rw [sourceNodesEquation] at sourceCompiled
          simp at sourceCompiled
      | some sourceNodes =>
          rw [sourceNodesEquation] at sourceCompiled
          cases sourceChildrenEquation :
              ConcreteElaboration.compileChildrenWith? definitions source.val
                (ConcreteElaboration.compileRegion? definitions source.val
                  fuel)
                (sourceContext.extend region)
                (source.val.childrenOf region) with
          | none =>
              rw [sourceChildrenEquation] at sourceCompiled
              simp at sourceCompiled
          | some sourceChildren =>
              rw [sourceChildrenEquation] at sourceCompiled
              cases targetNodesEquation :
                  ConcreteElaboration.compileNodes? definitions
                    (Target source removed)
                    (targetContext.extend
                      (targetRegion source removed region))
                    ((Target source removed).nodesAt
                      (targetRegion source removed region)) with
              | none =>
                  rw [targetNodesEquation] at targetCompiled
                  simp at targetCompiled
              | some targetNodes =>
                  rw [targetNodesEquation] at targetCompiled
                  cases targetChildrenEquation :
                      ConcreteElaboration.compileChildrenWith? definitions
                        (Target source removed)
                        (ConcreteElaboration.compileRegion? definitions
                          (Target source removed) fuel)
                        (targetContext.extend
                          (targetRegion source removed region))
                        ((Target source removed).childrenOf
                          (targetRegion source removed region)) with
                  | none =>
                      rw [targetChildrenEquation] at targetCompiled
                      simp at targetCompiled
                  | some targetChildren =>
                      rw [targetChildrenEquation] at targetCompiled
                      have sourceBodyExact :
                          ConcreteElaboration.finishRegion source.val
                              sourceContext region
                              (.mk (sourceNodes.append sourceChildren)) =
                            sourceBody :=
                        Option.some.inj sourceCompiled
                      have targetBodyExact :
                          ConcreteElaboration.finishRegion
                              (Target source removed) targetContext
                              (targetRegion source removed region)
                              (.mk (targetNodes.append targetChildren)) =
                            targetBody :=
                        Option.some.inj targetCompiled
                      subst sourceBody
                      subst targetBody
                      have sourceExtendedNodup :
                          (sourceContext.extend region).ids.Nodup :=
                        ConcreteElaboration.extend_nodup definitions source.val
                          source.property sourceContext region above
                      obtain ⟨expectedTargetNodes, expectedTargetCompiled,
                          sourceNodesExact⟩ :=
                        compileRegionNodes_reflect source removed
                          targetWellFormed removedEndpoints
                          (targetContext.extend
                            (targetRegion source removed region))
                          (sourceContext.extend region)
                          (extend_contexts_correspond source removed correspond
                            region)
                          sourceExtendedNodup region sourceNodesEquation
                      have targetNodesExact :
                          expectedTargetNodes = targetNodes :=
                        Option.some.inj
                          (expectedTargetCompiled.symm.trans
                            targetNodesEquation)
                      subst expectedTargetNodes
                      have sourceChildrenMapped :
                          ConcreteElaboration.compileChildrenWith? definitions
                              source.val
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (sourceContext.extend region)
                              (((Target source removed).childrenOf
                                (targetRegion source removed region)).map
                                (sourceRegion source removed)) =
                            some sourceChildren := by
                        rw [childrenOf_sources]
                        exact sourceChildrenEquation
                      rw [ConcreteElaboration.denote_finishRegion,
                        ConcreteElaboration.denote_finishRegion]
                      constructor
                      · rintro ⟨targetValues, targetCore⟩
                        obtain ⟨sourceValues, extendedEnvironments⟩ :=
                          extendEnvironmentsCorrespond_target source removed
                            targetContext sourceContext correspond region
                            sourceExtendedNodup
                            (fun same => outside
                              (same ▸ source.val.encloses_refl region))
                            pre specified targetEnv sourceEnv environments
                            targetValues
                        refine ⟨sourceValues, ?_⟩
                        simp only [denoteRegion, denoteItemSeq_append] at targetCore
                        simp only [denoteRegion, denoteItemSeq_append]
                        refine ⟨?_, ?_⟩
                        · rw [sourceNodesExact,
                            denoteItemSeq_renameWires,
                            extendedEnvironments.surviving]
                          exact targetCore.1
                        · exact
                            (compileChildren_corresponding_denotation source
                              removed
                              (targetContext.extend
                                (targetRegion source removed region))
                              (sourceContext.extend region)
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                (Target source removed) fuel)
                              ((Target source removed).childrenOf
                                (targetRegion source removed region))
                              sourceChildren targetChildren
                              sourceChildrenMapped targetChildrenEquation pre
                              definitionEnv
                              (ConcreteElaboration.extendEnvironment
                                (Target source removed) targetContext
                                (targetRegion source removed region)
                                targetValues targetEnv)
                              (ConcreteElaboration.extendEnvironment source.val
                                sourceContext region sourceValues sourceEnv)
                              (by
                                intro targetChild targetMember childSource
                                  childTarget childSourceCompiled
                                  childTargetCompiled
                                have sourceMember :
                                    sourceRegion source removed targetChild ∈
                                      source.val.childrenOf region := by
                                  rw [← childrenOf_sources source removed
                                    region]
                                  exact List.mem_map.mpr
                                    ⟨targetChild, targetMember, rfl⟩
                                exact
                                  induction
                                    (targetContext.extend
                                      (targetRegion source removed region))
                                    (sourceContext.extend region)
                                    (extend_contexts_correspond source removed
                                      correspond region)
                                    (sourceRegion source removed targetChild)
                                    (ConcreteElaboration.extend_above_child
                                      definitions source.val source.property
                                      sourceContext region
                                      (sourceRegion source removed targetChild)
                                      above
                                      (ConcreteElaboration.mem_childrenOf
                                        source.val region
                                        (sourceRegion source removed
                                          targetChild)
                                        sourceMember))
                                    (child_outside source removed region
                                      (sourceRegion source removed targetChild)
                                      outside sourceMember)
                                    childSource childTarget childSourceCompiled
                                    (by
                                      simpa only [targetRegion_sourceRegion]
                                        using childTargetCompiled)
                                    pre definitionEnv
                                    specified _ _ extendedEnvironments)
                            ).mp targetCore.2
                      · rintro ⟨sourceValues, sourceCore⟩
                        obtain ⟨targetValues, extendedEnvironments⟩ :=
                          extendEnvironmentsCorrespond_source source removed
                            targetContext sourceContext correspond region
                            sourceExtendedNodup
                            (fun same => outside
                              (same ▸ source.val.encloses_refl region))
                            pre specified targetEnv sourceEnv environments
                            sourceValues
                        refine ⟨targetValues, ?_⟩
                        simp only [denoteRegion, denoteItemSeq_append] at sourceCore
                        simp only [denoteRegion, denoteItemSeq_append]
                        refine ⟨?_, ?_⟩
                        · rw [sourceNodesExact,
                            denoteItemSeq_renameWires,
                            extendedEnvironments.surviving] at sourceCore
                          exact sourceCore.1
                        · exact
                            (compileChildren_corresponding_denotation source
                              removed
                              (targetContext.extend
                                (targetRegion source removed region))
                              (sourceContext.extend region)
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                (Target source removed) fuel)
                              ((Target source removed).childrenOf
                                (targetRegion source removed region))
                              sourceChildren targetChildren
                              sourceChildrenMapped targetChildrenEquation pre
                              definitionEnv
                              (ConcreteElaboration.extendEnvironment
                                (Target source removed) targetContext
                                (targetRegion source removed region)
                                targetValues targetEnv)
                              (ConcreteElaboration.extendEnvironment source.val
                                sourceContext region sourceValues sourceEnv)
                              (by
                                intro targetChild targetMember childSource
                                  childTarget childSourceCompiled
                                  childTargetCompiled
                                have sourceMember :
                                    sourceRegion source removed targetChild ∈
                                      source.val.childrenOf region := by
                                  rw [← childrenOf_sources source removed
                                    region]
                                  exact List.mem_map.mpr
                                    ⟨targetChild, targetMember, rfl⟩
                                exact
                                  induction
                                    (targetContext.extend
                                      (targetRegion source removed region))
                                    (sourceContext.extend region)
                                    (extend_contexts_correspond source removed
                                      correspond region)
                                    (sourceRegion source removed targetChild)
                                    (ConcreteElaboration.extend_above_child
                                      definitions source.val source.property
                                      sourceContext region
                                      (sourceRegion source removed targetChild)
                                      above
                                      (ConcreteElaboration.mem_childrenOf
                                        source.val region
                                        (sourceRegion source removed
                                          targetChild)
                                        sourceMember))
                                    (child_outside source removed region
                                      (sourceRegion source removed targetChild)
                                      outside sourceMember)
                                    childSource childTarget childSourceCompiled
                                    (by
                                      simpa only [targetRegion_sourceRegion]
                                        using childTargetCompiled)
                                    pre definitionEnv
                                    specified _ _ extendedEnvironments)
                            ).mpr sourceCore.2

/--
The unbound body at the removed wire's own scope preserves denotation under
one exact corresponding full-visible environment.
-/
theorem compileRegionBody_corresponding_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (fuel : Nat)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (atRemovedScope :
      region = (source.val.wires removed).scope)
    (above :
      ConcreteElaboration.ContextAbove source.val sourceContext region)
    (sourceBody :
      Region definitions (sourceContext.extend region).sigs)
    (targetBody :
      Region definitions
        (targetContext.extend
          (targetRegion source removed region)).sigs)
    (sourceCompiled :
      compileRegionBody? definitions source.val fuel region sourceContext =
        some sourceBody)
    (targetCompiled :
      compileRegionBody? definitions (Target source removed) fuel
          (targetRegion source removed region) targetContext =
        some targetBody)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetEnv :
      Env pre
        (targetContext.extend
          (targetRegion source removed region)).sigs)
    (sourceEnv : Env pre (sourceContext.extend region).sigs)
    (environments :
      EnvironmentsCorrespond source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        pre specified targetEnv sourceEnv) :
    denoteRegion pre definitionEnv targetEnv targetBody ↔
      denoteRegion pre definitionEnv sourceEnv sourceBody := by
  cases sourceNodesEquation :
      ConcreteElaboration.compileNodes? definitions source.val
        (sourceContext.extend region) (source.val.nodesAt region) with
  | none =>
      simp [compileRegionBody?, sourceNodesEquation] at sourceCompiled
  | some sourceNodes =>
      cases sourceChildrenEquation :
          ConcreteElaboration.compileChildrenWith? definitions source.val
            (ConcreteElaboration.compileRegion? definitions source.val fuel)
            (sourceContext.extend region) (source.val.childrenOf region) with
      | none =>
          simp [compileRegionBody?, sourceNodesEquation,
            sourceChildrenEquation] at sourceCompiled
      | some sourceChildren =>
          have sourceBodyExact :
              (.mk (sourceNodes.append sourceChildren) :
                Region definitions (sourceContext.extend region).sigs) =
                sourceBody := by
            apply Option.some.inj
            simpa [compileRegionBody?, sourceNodesEquation,
              sourceChildrenEquation] using sourceCompiled
          subst sourceBody
          cases targetNodesEquation :
              ConcreteElaboration.compileNodes? definitions
                (Target source removed)
                (targetContext.extend
                  (targetRegion source removed region))
                ((Target source removed).nodesAt
                  (targetRegion source removed region)) with
          | none =>
              simp [compileRegionBody?, targetNodesEquation] at targetCompiled
          | some targetNodes =>
              cases targetChildrenEquation :
                  ConcreteElaboration.compileChildrenWith? definitions
                    (Target source removed)
                    (ConcreteElaboration.compileRegion? definitions
                      (Target source removed) fuel)
                    (targetContext.extend
                      (targetRegion source removed region))
                    ((Target source removed).childrenOf
                      (targetRegion source removed region)) with
              | none =>
                  simp [compileRegionBody?, targetNodesEquation,
                    targetChildrenEquation] at targetCompiled
              | some targetChildren =>
                  have targetBodyExact :
                      (.mk (targetNodes.append targetChildren) :
                        Region definitions
                          (targetContext.extend
                            (targetRegion source removed region)).sigs) =
                        targetBody := by
                    apply Option.some.inj
                    simpa [compileRegionBody?, targetNodesEquation,
                      targetChildrenEquation] using targetCompiled
                  subst targetBody
                  have sourceExtendedNodup :
                      (sourceContext.extend region).ids.Nodup :=
                    ConcreteElaboration.extend_nodup definitions source.val
                      source.property sourceContext region above
                  obtain ⟨expectedTargetNodes, expectedTargetCompiled,
                      sourceNodesExact⟩ :=
                    compileRegionNodes_reflect source removed targetWellFormed
                      removedEndpoints
                      (targetContext.extend
                        (targetRegion source removed region))
                      (sourceContext.extend region)
                      (extend_contexts_correspond source removed correspond
                        region)
                      sourceExtendedNodup region sourceNodesEquation
                  have targetNodesExact :
                      expectedTargetNodes = targetNodes :=
                    Option.some.inj
                      (expectedTargetCompiled.symm.trans targetNodesEquation)
                  subst expectedTargetNodes
                  have sourceChildrenMapped :
                      ConcreteElaboration.compileChildrenWith? definitions
                          source.val
                          (ConcreteElaboration.compileRegion? definitions
                            source.val fuel)
                          (sourceContext.extend region)
                          (((Target source removed).childrenOf
                            (targetRegion source removed region)).map
                            (sourceRegion source removed)) =
                        some sourceChildren := by
                    rw [childrenOf_sources]
                    exact sourceChildrenEquation
                  simp only [denoteRegion, denoteItemSeq_append]
                  exact and_congr
                    (by
                      rw [sourceNodesExact, denoteItemSeq_renameWires,
                        environments.surviving])
                    (compileChildren_corresponding_denotation source removed
                      (targetContext.extend
                        (targetRegion source removed region))
                      (sourceContext.extend region)
                      (ConcreteElaboration.compileRegion? definitions
                        source.val fuel)
                      (ConcreteElaboration.compileRegion? definitions
                        (Target source removed) fuel)
                      ((Target source removed).childrenOf
                        (targetRegion source removed region))
                      sourceChildren targetChildren sourceChildrenMapped
                      targetChildrenEquation pre definitionEnv targetEnv
                      sourceEnv (by
                        intro targetChild targetMember childSource childTarget
                          childSourceCompiled childTargetCompiled
                        have sourceMember :
                            sourceRegion source removed targetChild ∈
                              source.val.childrenOf region := by
                          rw [← childrenOf_sources source removed region]
                          exact List.mem_map.mpr
                            ⟨targetChild, targetMember, rfl⟩
                        exact
                          compileRegion_corresponding_denotation source removed
                            targetWellFormed removedEndpoints fuel
                            (targetContext.extend
                              (targetRegion source removed region))
                            (sourceContext.extend region)
                            (extend_contexts_correspond source removed
                              correspond region)
                            (sourceRegion source removed targetChild)
                            (ConcreteElaboration.extend_above_child definitions
                              source.val source.property sourceContext region
                              (sourceRegion source removed targetChild) above
                              (ConcreteElaboration.mem_childrenOf source.val
                                region
                                (sourceRegion source removed targetChild)
                                sourceMember))
                            (by
                              simpa only [← atRemovedScope] using
                                child_outside_parent source region
                                  (sourceRegion source removed targetChild)
                                  sourceMember)
                            childSource childTarget childSourceCompiled
                            (by
                              simpa only [targetRegion_sourceRegion] using
                                childTargetCompiled)
                            pre definitionEnv specified targetEnv sourceEnv
                            environments))

/--
Reflect one accepted fueled source-region compilation through singleton-wire
deletion. This theorem owns the only ordinary recursive traversal used by the
frame reflector.
-/
theorem compileRegion_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = []) :
    ∀ (fuel : Nat)
      (targetContext :
        ConcreteElaboration.WireContext (Target source removed))
      (sourceContext : ConcreteElaboration.WireContext source.val)
      (_correspond : ContextsCorrespond source removed
        targetContext sourceContext)
      (region : source.val.RegionId)
      (_above :
        ConcreteElaboration.ContextAbove source.val sourceContext region)
      {sourceBody : Region definitions sourceContext.sigs},
      ConcreteElaboration.compileRegion? definitions source.val fuel
          region sourceContext =
        some sourceBody →
      ∃ targetBody : Region definitions targetContext.sigs,
        ConcreteElaboration.compileRegion? definitions
            (Target source removed) fuel
            (targetRegion source removed region) targetContext =
            some targetBody ∧
          ∀ (removedAbsent : removed ∉ sourceContext.ids)
            (_outside :
              ¬source.val.Encloses region
                (source.val.wires removed).scope)
            (pre : PreModel.{u})
            (definitionEnv : DefinitionEnv pre definitions)
            (targetEnv : Env pre targetContext.sigs),
            denoteRegion pre definitionEnv targetEnv targetBody ↔
              denoteRegion pre definitionEnv
                (Env.comp targetEnv
                  (contextProjection source removed targetContext
                    sourceContext _correspond removedAbsent))
                sourceBody := by
  intro fuel
  induction fuel with
  | zero =>
      intro targetContext sourceContext correspond region above sourceBody
        sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel induction =>
      intro targetContext sourceContext correspond region above sourceBody
        sourceCompiled
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled
      cases sourceNodesEquation :
          ConcreteElaboration.compileNodes? definitions source.val
            (sourceContext.extend region) (source.val.nodesAt region) with
      | none =>
          rw [sourceNodesEquation] at sourceCompiled
          simp at sourceCompiled
      | some sourceNodes =>
          rw [sourceNodesEquation] at sourceCompiled
          cases sourceChildrenEquation :
              ConcreteElaboration.compileChildrenWith? definitions source.val
                (ConcreteElaboration.compileRegion? definitions source.val
                  fuel)
                (sourceContext.extend region)
                (source.val.childrenOf region) with
          | none =>
              rw [sourceChildrenEquation] at sourceCompiled
              simp at sourceCompiled
          | some sourceChildren =>
              rw [sourceChildrenEquation] at sourceCompiled
              have sourceBodyExact :
                  ConcreteElaboration.finishRegion source.val sourceContext
                      region
                      (.mk (sourceNodes.append sourceChildren)) =
                    sourceBody :=
                Option.some.inj sourceCompiled
              subst sourceBody
              have sourceExtendedNodup :
                  (sourceContext.extend region).ids.Nodup :=
                ConcreteElaboration.extend_nodup definitions source.val
                  source.property sourceContext region above
              let targetExtended :=
                targetContext.extend (targetRegion source removed region)
              let sourceExtended := sourceContext.extend region
              have extendedCorrespond :
                  ContextsCorrespond source removed
                    targetExtended sourceExtended := by
                exact extend_contexts_correspond source removed correspond
                  region
              obtain ⟨targetNodes, targetNodesCompiled, sourceNodesExact⟩ :=
                compileRegionNodes_reflect source removed targetWellFormed
                  removedEndpoints targetExtended sourceExtended
                  extendedCorrespond sourceExtendedNodup region
                  sourceNodesEquation
              have sourceChildrenMapped :
                  ConcreteElaboration.compileChildrenWith? definitions
                      source.val
                      (ConcreteElaboration.compileRegion? definitions
                        source.val fuel)
                      sourceExtended
                      (((Target source removed).childrenOf
                        (targetRegion source removed region)).map
                        (sourceRegion source removed)) =
                    some sourceChildren := by
                rw [childrenOf_sources]
                exact sourceChildrenEquation
              obtain ⟨targetChildren, targetChildrenCompiled,
                  targetChildrenLaw⟩ :=
                compileChildren_reflect_of source removed targetExtended
                  sourceExtended
                  (ConcreteElaboration.compileRegion? definitions
                    source.val fuel)
                  (ConcreteElaboration.compileRegion? definitions
                    (Target source removed) fuel)
                  extendedCorrespond
                  ((Target source removed).childrenOf
                    (targetRegion source removed region))
                  sourceChildrenMapped (by
                    intro targetChild targetMember childBody childCompiled
                    have sourceMember :
                        sourceRegion source removed targetChild ∈
                          source.val.childrenOf region := by
                      rw [← childrenOf_sources source removed region]
                      exact List.mem_map.mpr
                        ⟨targetChild, targetMember, rfl⟩
                    have childData :=
                      ConcreteElaboration.mem_childrenOf source.val region
                        (sourceRegion source removed targetChild)
                        sourceMember
                    obtain ⟨targetBody, targetCompiled, targetLaw⟩ :=
                      induction targetExtended sourceExtended
                        extendedCorrespond
                        (sourceRegion source removed targetChild)
                        (ConcreteElaboration.extend_above_child definitions
                          source.val source.property sourceContext region
                          (sourceRegion source removed targetChild) above
                          childData)
                        childCompiled
                    refine ⟨targetBody, ?_, ?_⟩
                    · simpa only [targetRegion_sourceRegion] using
                        targetCompiled
                    · exact targetLaw)
              refine
                ⟨ConcreteElaboration.finishRegion
                    (Target source removed) targetContext
                    (targetRegion source removed region)
                    (.mk (targetNodes.append targetChildren)), ?_, ?_⟩
              · simp only [ConcreteElaboration.compileRegion?]
                rw [targetNodesCompiled, targetChildrenCompiled]
                rfl
              · intro removedAbsent outside pre definitionEnv targetEnv
                apply finishRetainedRegion_equiv source removed targetContext
                  sourceContext correspond removedAbsent region outside above
                intro currentPre currentDefinitions currentTarget
                simp only [denoteRegion, denoteItemSeq_append]
                have nodeLaw :
                    denoteItemSeq currentPre currentDefinitions currentTarget
                          targetNodes ↔
                      denoteItemSeq currentPre currentDefinitions
                        (Env.comp currentTarget
                          (contextProjection source removed targetExtended
                            sourceExtended extendedCorrespond
                            (removed_absent_extend source removed sourceContext
                              region removedAbsent
                              (fun same => outside
                                (same ▸ source.val.encloses_refl region)))))
                        sourceNodes := by
                  rw [sourceNodesExact, denoteItemSeq_renameWires,
                    contextProjection_embedding_environment source removed
                      targetExtended sourceExtended extendedCorrespond
                      sourceExtendedNodup
                      (removed_absent_extend source removed sourceContext
                        region removedAbsent
                        (fun same => outside
                          (same ▸ source.val.encloses_refl region)))
                      currentPre currentTarget]
                exact and_congr nodeLaw
                  (targetChildrenLaw
                    (removed_absent_extend source removed sourceContext region
                      removedAbsent
                      (fun same => outside
                        (same ▸ source.val.encloses_refl region)))
                    (fun targetChild targetMember =>
                      child_outside source removed region
                        (sourceRegion source removed targetChild) outside
                        (by
                          rw [← childrenOf_sources source removed region]
                          exact List.mem_map.mpr
                            ⟨targetChild, targetMember, rfl⟩))
                    currentPre currentDefinitions currentTarget)

/--
Reflect the unbound body owned by one copied region through the same fueled
ordinary traversal.
-/
theorem compileRegionBody_reflect
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetWellFormed : (Target source removed).WellFormed definitions)
    (removedEndpoints : (source.val.wires removed).endpoints = [])
    (fuel : Nat)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (above :
      ConcreteElaboration.ContextAbove source.val sourceContext region)
    {sourceBody :
      Region definitions (sourceContext.extend region).sigs}
    (sourceCompiled :
      compileRegionBody? definitions source.val fuel region sourceContext =
        some sourceBody) :
    ∃ targetBody :
        Region definitions
          (targetContext.extend
            (targetRegion source removed region)).sigs,
      compileRegionBody? definitions (Target source removed) fuel
          (targetRegion source removed region) targetContext =
        some targetBody := by
  cases sourceNodesEquation :
      ConcreteElaboration.compileNodes? definitions source.val
        (sourceContext.extend region) (source.val.nodesAt region) with
  | none =>
      simp [compileRegionBody?, sourceNodesEquation] at sourceCompiled
  | some sourceNodes =>
      cases sourceChildrenEquation :
          ConcreteElaboration.compileChildrenWith? definitions source.val
            (ConcreteElaboration.compileRegion? definitions source.val fuel)
            (sourceContext.extend region) (source.val.childrenOf region) with
      | none =>
          simp [compileRegionBody?, sourceNodesEquation,
            sourceChildrenEquation] at sourceCompiled
      | some sourceChildren =>
          have sourceFull :
              ConcreteElaboration.compileRegion? definitions source.val
                  (fuel + 1) region sourceContext =
                some
                  (ConcreteElaboration.finishRegion source.val sourceContext
                    region (.mk (sourceNodes.append sourceChildren))) := by
            simp [ConcreteElaboration.compileRegion?,
              sourceNodesEquation, sourceChildrenEquation]
          obtain ⟨targetFull, targetCompiled, _targetLaw⟩ :=
            compileRegion_reflect.{0} source removed targetWellFormed
              removedEndpoints (fuel + 1) targetContext sourceContext
              correspond region above sourceFull
          simp only [ConcreteElaboration.compileRegion?] at targetCompiled
          cases targetNodesEquation :
              ConcreteElaboration.compileNodes? definitions
                (Target source removed)
                (targetContext.extend
                  (targetRegion source removed region))
                ((Target source removed).nodesAt
                  (targetRegion source removed region)) with
          | none =>
              rw [targetNodesEquation] at targetCompiled
              simp at targetCompiled
          | some targetNodes =>
              rw [targetNodesEquation] at targetCompiled
              cases targetChildrenEquation :
                  ConcreteElaboration.compileChildrenWith? definitions
                    (Target source removed)
                    (ConcreteElaboration.compileRegion? definitions
                      (Target source removed) fuel)
                    (targetContext.extend
                      (targetRegion source removed region))
                    ((Target source removed).childrenOf
                      (targetRegion source removed region)) with
              | none =>
                  rw [targetChildrenEquation] at targetCompiled
                  simp at targetCompiled
              | some targetChildren =>
                  refine
                    ⟨.mk (targetNodes.append targetChildren), ?_⟩
                  simp [compileRegionBody?, targetNodesEquation,
                    targetChildrenEquation]

/--
Above the removed wire, the canonical source environment is exactly the
ordinary deletion projection.
-/
theorem sourceEnvironmentFromTarget_eq_projection
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetEnv : Env pre targetContext.sigs) :
    sourceEnvironmentFromTarget source removed targetContext sourceContext
        correspond pre specified targetEnv =
      Env.comp targetEnv
        (contextProjection source removed targetContext sourceContext
          correspond removedAbsent) := by
  funext sig value
  have survives :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        removed := by
    intro same
    exact removedAbsent (same ▸
      InsertionCompilation.NaturalityInternal.origin_member source.val
        sourceContext.ids value)
  simp only [sourceEnvironmentFromTarget, dif_pos survives, Env.comp]
  apply congrArg (targetEnv sig)
  apply InsertionCompilation.NaturalityInternal.origin_injective
    (Target source removed) targetContext.ids
  · exact targetContext_nodup source removed targetContext sourceContext
      correspond sourceNodup
  · rw [survivingProjection_action, contextProjection_action]

/--
Recover the source binder witnesses from the canonical full source
environment.  The generic environment retraction closes the binder block;
there is no second positional deletion representation.
-/
theorem sourceEnvironmentFromTarget_extend_reconstruct
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond : ContextsCorrespond source removed
      targetContext sourceContext)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (removedAbsent : removed ∉ sourceContext.ids)
    (pre : PreModel.{u})
    (specified : pre.Domain (source.val.wires removed).sig)
    (targetValues :
      ConcreteElaboration.WireValues pre
        (((Target source removed).wiresAt
          (targetRegion source removed region)).map fun wire =>
            ((Target source removed).wires wire).sig))
    (targetOuter : Env pre targetContext.sigs) :
    let targetExtended :=
      ConcreteElaboration.extendEnvironment (Target source removed)
        targetContext (targetRegion source removed region)
        targetValues targetOuter
    let sourceExtended :=
      sourceEnvironmentFromTarget source removed
        (targetContext.extend (targetRegion source removed region))
        (sourceContext.extend region)
        (extend_contexts_correspond source removed correspond region)
        pre specified targetExtended
    ConcreteElaboration.extendEnvironment source.val sourceContext region
        (ConcreteElaboration.valuesFromEnvironmentFor source.val
          sourceContext.ids (source.val.wiresAt region) sourceExtended)
        (sourceEnvironmentFromTarget source removed targetContext
          sourceContext correspond pre specified targetOuter) =
      sourceExtended := by
  simp only
  apply extendEnvironment_from
  intro sig value
  have outerSurvives :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        removed := by
    intro same
    exact removedAbsent (same ▸
      InsertionCompilation.NaturalityInternal.origin_member source.val
        sourceContext.ids value)
  have extendedSurvives :
      ConcreteElaboration.WireContext.origin source.val
          (sourceContext.extend region).ids
          (ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) value) ≠
        removed := by
    intro same
    exact outerSurvives
      ((ConcreteElaboration.origin_appendRightVar source.val
        (source.val.wiresAt region) value).symm.trans same)
  simp only [sourceEnvironmentFromTarget, dif_pos extendedSurvives,
    dif_pos outerSurvives]
  rw [survivingProjection_appendRight source removed targetContext
    sourceContext correspond region sourceExtendedNodup value
    outerSurvives]
  exact
    ConcreteElaboration.extendEnvironment_appendRightVar
      (Target source removed) targetContext
      (targetRegion source removed region) targetValues targetOuter
      (survivingProjection source removed targetContext sourceContext
        correspond value outerSurvives)

/--
Close the unequal dying-scope binder blocks using the canonical
origin-indexed source environment.
-/
theorem finishDyingRegion_implication
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond :
      ContextsCorrespond source removed targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    (sourceExtendedNodup :
      (sourceContext.extend (source.val.wires removed).scope).ids.Nodup)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (targetOuterEnv : Env pre targetContext.sigs)
    (specified :
      ∀ retainedLocal :
          ConcreteElaboration.WireValues pre
            (((Target source removed).wiresAt
              (targetRegion source removed
                (source.val.wires removed).scope)).map
              fun wire => ((Target source removed).wires wire).sig),
        pre.Domain (source.val.wires removed).sig)
    (targetBody :
      Region definitions
        (targetContext.extend
          (targetRegion source removed
            (source.val.wires removed).scope)).sigs)
    (sourceBody :
      Region definitions
        (sourceContext.extend
          (source.val.wires removed).scope).sigs)
    (localBodyLaw :
      ∀ (chosen : pre.Domain (source.val.wires removed).sig)
        (targetEnv :
          Env pre
            (targetContext.extend
              (targetRegion source removed
                (source.val.wires removed).scope)).sigs),
        denoteRegion pre definitionEnv targetEnv targetBody →
          denoteRegion pre definitionEnv
            (sourceEnvironmentFromTarget source removed
              (targetContext.extend
                (targetRegion source removed
                  (source.val.wires removed).scope))
              (sourceContext.extend
                (source.val.wires removed).scope)
              (extend_contexts_correspond source removed correspond
                (source.val.wires removed).scope)
              pre chosen targetEnv)
            sourceBody) :
    denoteRegion pre definitionEnv targetOuterEnv
        (ConcreteElaboration.finishRegion
          (Target source removed) targetContext
          (targetRegion source removed
            (source.val.wires removed).scope)
          targetBody) →
      denoteRegion pre definitionEnv
        (Env.comp targetOuterEnv
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        (ConcreteElaboration.finishRegion source.val sourceContext
          (source.val.wires removed).scope sourceBody) := by
  intro targetFinished
  obtain ⟨targetValues, targetCore⟩ :=
    (ConcreteElaboration.denote_finishRegion definitions
      (Target source removed) targetContext
      (targetRegion source removed
        (source.val.wires removed).scope)
      pre definitionEnv targetOuterEnv targetBody).mp targetFinished
  let chosen := specified targetValues
  let targetExtended :=
    ConcreteElaboration.extendEnvironment (Target source removed)
      targetContext
      (targetRegion source removed (source.val.wires removed).scope)
      targetValues targetOuterEnv
  let sourceExtended :=
    sourceEnvironmentFromTarget source removed
      (targetContext.extend
        (targetRegion source removed (source.val.wires removed).scope))
      (sourceContext.extend (source.val.wires removed).scope)
      (extend_contexts_correspond source removed correspond
        (source.val.wires removed).scope)
      pre chosen targetExtended
  let sourceValues :=
    ConcreteElaboration.valuesFromEnvironmentFor source.val
      sourceContext.ids
      (source.val.wiresAt (source.val.wires removed).scope)
      sourceExtended
  apply
    (ConcreteElaboration.denote_finishRegion definitions source.val
      sourceContext (source.val.wires removed).scope
      pre definitionEnv
      (Env.comp targetOuterEnv
        (contextProjection source removed targetContext sourceContext
          correspond removedAbsent))
      sourceBody).mpr
  refine ⟨sourceValues, ?_⟩
  have reconstructed :
      ConcreteElaboration.extendEnvironment source.val sourceContext
          (source.val.wires removed).scope sourceValues
          (sourceEnvironmentFromTarget source removed targetContext
            sourceContext correspond pre chosen targetOuterEnv) =
        sourceExtended := by
    exact
      sourceEnvironmentFromTarget_extend_reconstruct source removed
        targetContext sourceContext correspond
        (source.val.wires removed).scope sourceExtendedNodup removedAbsent
        pre chosen targetValues targetOuterEnv
  rw [sourceEnvironmentFromTarget_eq_projection source removed
    targetContext sourceContext correspond
    (by
      have parts := sourceExtendedNodup
      rw [ConcreteElaboration.WireContext.extend,
        List.nodup_append] at parts
      exact parts.2.1)
    removedAbsent pre chosen targetOuterEnv] at reconstructed
  rw [reconstructed]
  exact localBodyLaw chosen targetExtended targetCore

/--
Close the unequal dying-scope binder blocks in both directions. The
plain-to-bound direction uses the caller's inhabitant; the bound-to-plain
direction recovers the removed value from the source binder witness.
-/
theorem finishDyingRegion_equivalence
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (targetContext :
      ConcreteElaboration.WireContext (Target source removed))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (correspond :
      ContextsCorrespond source removed targetContext sourceContext)
    (removedAbsent : removed ∉ sourceContext.ids)
    (sourceExtendedNodup :
      (sourceContext.extend (source.val.wires removed).scope).ids.Nodup)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (targetOuterEnv : Env pre targetContext.sigs)
    (specified :
      ∀ retainedLocal :
          ConcreteElaboration.WireValues pre
            (((Target source removed).wiresAt
              (targetRegion source removed
                (source.val.wires removed).scope)).map
              fun wire => ((Target source removed).wires wire).sig),
        pre.Domain (source.val.wires removed).sig)
    (targetBody :
      Region definitions
        (targetContext.extend
          (targetRegion source removed
            (source.val.wires removed).scope)).sigs)
    (sourceBody :
      Region definitions
        (sourceContext.extend
          (source.val.wires removed).scope).sigs)
    (localBodyEquivalence :
      ∀ (chosen : pre.Domain (source.val.wires removed).sig)
        (targetEnv :
          Env pre
            (targetContext.extend
              (targetRegion source removed
                (source.val.wires removed).scope)).sigs),
        denoteRegion pre definitionEnv targetEnv targetBody ↔
          denoteRegion pre definitionEnv
            (sourceEnvironmentFromTarget source removed
              (targetContext.extend
                (targetRegion source removed
                  (source.val.wires removed).scope))
              (sourceContext.extend
                (source.val.wires removed).scope)
              (extend_contexts_correspond source removed correspond
                (source.val.wires removed).scope)
              pre chosen targetEnv)
            sourceBody) :
    denoteRegion pre definitionEnv targetOuterEnv
        (ConcreteElaboration.finishRegion
          (Target source removed) targetContext
          (targetRegion source removed
            (source.val.wires removed).scope)
          targetBody) ↔
      denoteRegion pre definitionEnv
        (Env.comp targetOuterEnv
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        (ConcreteElaboration.finishRegion source.val sourceContext
          (source.val.wires removed).scope sourceBody) := by
  constructor
  · exact
      finishDyingRegion_implication source removed targetContext
        sourceContext correspond removedAbsent sourceExtendedNodup pre
        definitionEnv targetOuterEnv specified targetBody sourceBody
        (fun chosen targetEnv =>
          (localBodyEquivalence chosen targetEnv).mp)
  · intro sourceFinished
    obtain ⟨sourceValues, sourceCore⟩ :=
      (ConcreteElaboration.denote_finishRegion definitions source.val
        sourceContext (source.val.wires removed).scope pre definitionEnv
        (Env.comp targetOuterEnv
          (contextProjection source removed targetContext sourceContext
            correspond removedAbsent))
        sourceBody).mp sourceFinished
    obtain ⟨chosen, targetValues, environments⟩ :=
      dyingScopeEnvironmentsCorrespond_source source removed targetContext
        sourceContext correspond removedAbsent sourceExtendedNodup pre
        targetOuterEnv sourceValues
    apply
      (ConcreteElaboration.denote_finishRegion definitions
        (Target source removed) targetContext
        (targetRegion source removed
          (source.val.wires removed).scope)
        pre definitionEnv targetOuterEnv targetBody).mpr
    refine ⟨targetValues, ?_⟩
    apply (localBodyEquivalence chosen _).mpr
    rw [← environments.source_eq sourceExtendedNodup]
    exact sourceCore

end ExhaustedWireRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
