import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveShapes

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

/-- Ordered node compilation is natural under inclusion into a larger
duplicate-free context of the same checked diagram. -/
theorem recursiveCompileNodes?_contextEmbedding
    (checked : CheckedDiagram definitions)
    (sourceContext targetContext :
      ConcreteElaboration.WireContext checked.val)
    (targetNodup : targetContext.ids.Nodup)
    (visible : ∀ wire, wire ∈ sourceContext.ids →
      wire ∈ targetContext.ids)
    (nodes : List checked.val.NodeId)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions checked.val sourceContext
        nodes = some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      ConcreteElaboration.compileNodes? definitions checked.val targetContext
          nodes = some targetItems ∧
        targetItems = sourceItems.renameWires
          (InsertionCompilation.NaturalityInternal.contextEmbedding
            checked.val checked.val sourceContext.ids targetContext.ids
            (fun wire => wire) (fun _ => rfl) visible) := by
  let embedding : WireRenaming sourceContext.sigs targetContext.sigs :=
    InsertionCompilation.NaturalityInternal.contextEmbedding
      checked.val checked.val sourceContext.ids targetContext.ids
      (fun wire => wire) (fun _ => rfl) visible
  induction nodes generalizing sourceItems with
  | nil =>
      simp only [ConcreteElaboration.compileNodes?, Option.some.injEq]
        at sourceCompiled ⊢
      subst sourceItems
      exact ⟨.nil, rfl, rfl⟩
  | cons head tail induction =>
      simp only [ConcreteElaboration.compileNodes?] at sourceCompiled ⊢
      cases sourceHeadEquation :
          ConcreteElaboration.Internal.compileNode? definitions checked.val
            sourceContext head with
      | none => simp [sourceHeadEquation] at sourceCompiled
      | some sourceHead =>
          cases sourceTailEquation :
              ConcreteElaboration.compileNodes? definitions checked.val
                sourceContext tail with
          | none => simp [sourceHeadEquation, sourceTailEquation] at sourceCompiled
          | some sourceTail =>
              have sourceItemsExact :
                  sourceItems = .cons sourceHead sourceTail := by
                exact (Option.some.inj (by
                  simpa [sourceHeadEquation, sourceTailEquation] using
                    sourceCompiled)).symm
              subst sourceItems
              have embeddingOrigin : ∀ {signature : Sig}
                  (value : Var sourceContext.sigs signature),
                  ConcreteElaboration.WireContext.origin checked.val
                      targetContext.ids (embedding value) =
                    ConcreteElaboration.WireContext.origin checked.val
                      sourceContext.ids value := by
                intro signature value
                exact InsertionCompilation.NaturalityInternal.contextEmbedding_origin
                  checked.val checked.val sourceContext.ids targetContext.ids
                  (fun wire => wire) (fun _ => rfl) visible value
              have targetHeadEquation :=
                ConcreteElaboration.compileNode?_natural checked.property
                  targetNodup embedding (fun wire => wire) embeddingOrigin
                  (fun region => region) (leftNode := head) (rightNode := head)
                  (by cases checked.val.nodes head <;> rfl)
                  (by intro _port _wire incident; exact incident)
                  sourceHeadEquation
              obtain ⟨targetTail, targetTailEquation, targetTailExact⟩ :=
                induction sourceTailEquation
              refine ⟨.cons (sourceHead.renameWires embedding) targetTail,
                ?_, ?_⟩
              · simp [targetHeadEquation, targetTailEquation]
              · rw [targetTailExact]
                rfl

/-- The actual source variables available to retained ordinary nodes after
removing the acted relation head from a recursive compiler context. -/
def recursiveRetainedSourceContext
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (context : ConcreteElaboration.WireContext source.val) :
    ConcreteElaboration.WireContext source.val :=
  ⟨context.ids.filter fun sourceWire => decide (sourceWire ≠ wire)⟩

/-- The construction-owned checked image of a head-free recursive context. -/
def recursiveRetainedTargetContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (context : ConcreteElaboration.WireContext source.val) :
    ConcreteElaboration.WireContext result.checked.val :=
  ⟨(recursiveRetainedSourceContext source wire context).ids.map
    result.contextWireMap⟩

/-- Head filtering exposes exactly the carrier on which the checked argument
replacement has a signature-preserving context action. -/
def recursiveRetainedContext
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (context : ConcreteElaboration.WireContext source.val) :
    result.RetainedContext
      (recursiveRetainedSourceContext source wire context)
      (recursiveRetainedTargetContext result context) where
  ids_exact := rfl
  source_retained := by
    intro sourceWire member
    rw [arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]
    simp only [List.mem_singleton]
    exact of_decide_eq_true (List.mem_filter.mp member).2

/-- Every retained node in a covered recursive context compiles after the
changed head has been removed. -/
theorem recursiveCompileRetainedNodes?_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (result : ArgumentResult source wire)
    (region : source.val.RegionId)
    (context : ConcreteElaboration.WireContext source.val)
    (covers : context.Covers region) :
    ∃ items,
      ConcreteElaboration.compileNodes? definitions source.val
          (recursiveRetainedSourceContext source wire context)
          ((source.val.nodesAt region).filter fun node =>
            decide (node ∉ argumentSiteNodes result.sites)) = some items := by
  let nodes := (source.val.nodesAt region).filter fun node =>
    decide (node ∉ argumentSiteNodes result.sites)
  have nodeFacts : ∀ node, node ∈ nodes →
      node ∈ source.val.nodesAt region ∧
        node ∉ argumentSiteNodes result.sites := by
    intro node member
    exact ⟨(List.mem_filter.mp member).1,
      of_decide_eq_true (List.mem_filter.mp member).2⟩
  have compileList : ∀ selected : List source.val.NodeId,
      (∀ node, node ∈ selected →
        node ∈ source.val.nodesAt region ∧
          node ∉ argumentSiteNodes result.sites) →
      ∃ items,
        ConcreteElaboration.compileNodes? definitions source.val
          (recursiveRetainedSourceContext source wire context) selected =
            some items := by
    intro selected allMembers
    induction selected with
    | nil => exact ⟨.nil, rfl⟩
    | cons head tail induction =>
        have headFacts := allMembers head (by simp)
        obtain ⟨headItem, headCompiled⟩ :=
          ConcreteElaboration.compileNode?_complete_of_required_visible
            definitions source.val source.property
            (recursiveRetainedSourceContext source wire context) head (by
              intro port portRequired sourceWire sourceOwner
              have nodeRegion : (source.val.nodes head).region = region := by
                unfold ConcreteDiagram.nodesAt at headFacts
                exact eq_of_beq (List.mem_filter.mp headFacts.1).2
              have ownerEncloses : source.val.Encloses
                  (source.val.wires sourceWire).scope region := by
                have ownerScope :=
                  ConcreteElaboration.Internal.endpoint_scope definitions
                    source.val source.property ⟨head, port⟩ sourceWire
                    sourceOwner
                simpa [nodeRegion] using ownerScope
              apply List.mem_filter.mpr
              refine ⟨covers sourceWire ownerEncloses, decide_eq_true ?_⟩
              intro same
              subst sourceWire
              exact result.ownerOfRetainedNode_not_removed head headFacts.2
                port wire sourceOwner (by simp [ArgumentResult.sourceRemovedWires]))
        obtain ⟨tailItems, tailCompiled⟩ := induction (by
          intro node member
          exact allMembers node (by simp [member]))
        exact ⟨ItemSeq.cons headItem tailItems, by
          simp [ConcreteElaboration.compileNodes?, headCompiled,
            tailCompiled]⟩
  simpa [nodes] using compileList nodes nodeFacts

/-- Retained ordinary nodes at any recursive region compile in paired
head-free contexts and are related by the unique checked retained-wire map. -/
theorem recursiveRetainedNodePair_pruned
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (context : ConcreteElaboration.WireContext source.val)
    (covers : context.Covers region)
    (contextNodup : context.ids.Nodup) :
    ∃ (sourceItems : ItemSeq definitions
          (recursiveRetainedSourceContext source wire context).sigs)
      (targetItems : ItemSeq definitions
          (recursiveRetainedTargetContext result context).sigs),
      ConcreteElaboration.compileNodes? definitions source.val
          (recursiveRetainedSourceContext source wire context)
          ((source.val.nodesAt region).filter fun node =>
            decide (node ∉ argumentSiteNodes result.sites)) =
        some sourceItems ∧
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (recursiveRetainedTargetContext result context)
          (((replacementBase result.plan).nodesAt
              (retainedRegion source region)).map fun retained =>
            ConcreteWireQuantifier.Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained)) =
        some targetItems ∧
      targetItems = sourceItems.renameWires
        (recursiveRetainedContext source wire newArgument result accepted
          context).wireRenaming := by
  obtain ⟨sourceItems, sourceCompiled⟩ :=
    recursiveCompileRetainedNodes?_complete source wire result region context
      covers
  let retained := recursiveRetainedContext source wire newArgument result
    accepted context
  have sourceNodup :
      (recursiveRetainedSourceContext source wire context).ids.Nodup :=
    contextNodup.filter _
  have targetNodup :
      (recursiveRetainedTargetContext result context).ids.Nodup :=
    retained.target_nodup sourceNodup
  obtain ⟨targetItems, targetCompiled, targetExact⟩ :=
    retained.compileNodes_natural targetNodup
      (ArgumentResult.RetainedContext.nodesAt_retainedPrefix result region)
      sourceCompiled
  exact ⟨sourceItems, targetItems, sourceCompiled, targetCompiled,
    targetExact⟩

/-- Independent normalizations of the paired pruned contexts recover the
requested intrinsic block embedding whenever they commute on the retained
carrier.  No action on the changed relation head is required. -/
theorem recursiveRetainedNodePair_normalized
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (context : ConcreteElaboration.WireContext source.val)
    (covers : context.Covers region)
    (contextNodup : context.ids.Nodup)
    (sourceMap : WireRenaming
      (recursiveRetainedSourceContext source wire context).sigs
      normalizedSource)
    (targetMap : WireRenaming
      (recursiveRetainedTargetContext result context).sigs normalizedTarget)
    (embedding : WireRenaming normalizedSource normalizedTarget)
    (commutes : ∀ {signature : Sig}
      (value : Var
        (recursiveRetainedSourceContext source wire context).sigs signature),
      embedding (sourceMap value) =
        targetMap
          ((recursiveRetainedContext source wire newArgument result accepted
            context).wireRenaming value)) :
    ∃ (sourceItems : ItemSeq definitions
          (recursiveRetainedSourceContext source wire context).sigs)
      (targetItems : ItemSeq definitions
          (recursiveRetainedTargetContext result context).sigs),
      ConcreteElaboration.compileNodes? definitions source.val
          (recursiveRetainedSourceContext source wire context)
          ((source.val.nodesAt region).filter fun node =>
            decide (node ∉ argumentSiteNodes result.sites)) =
        some sourceItems ∧
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (recursiveRetainedTargetContext result context)
          (((replacementBase result.plan).nodesAt
              (retainedRegion source region)).map fun retained =>
            ConcreteWireQuantifier.Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained)) =
        some targetItems ∧
      targetItems.renameWires targetMap =
        (sourceItems.renameWires sourceMap).renameWires embedding := by
  obtain ⟨sourceItems, targetItems, sourceCompiled, targetCompiled,
      targetExact⟩ := recursiveRetainedNodePair_pruned source wire
    newArgument result accepted region context covers contextNodup
  refine ⟨sourceItems, targetItems, sourceCompiled, targetCompiled, ?_⟩
  subst targetItems
  let retainedMap : WireRenaming
      (recursiveRetainedSourceContext source wire context).sigs
      (recursiveRetainedTargetContext result context).sigs :=
    fun {_} value =>
      (recursiveRetainedContext source wire newArgument result accepted
        context).wireRenaming value
  let combined : WireRenaming
      (recursiveRetainedSourceContext source wire context).sigs
      normalizedTarget := fun {_} value => targetMap (retainedMap value)
  calc
    (sourceItems.renameWires retainedMap).renameWires targetMap =
        sourceItems.renameWires combined :=
      recursiveItemSeqRename_comp retainedMap targetMap combined
        (fun _ => rfl) sourceItems
    _ = sourceItems.renameWires
        (fun {_} value => embedding (sourceMap value)) :=
      recursiveItemSeqRename_eq _ _ (by
        intro signature value
        exact (commutes value).symm) sourceItems
    _ = (sourceItems.renameWires sourceMap).renameWires embedding :=
      (recursiveItemSeqRename_comp sourceMap embedding
        (fun {_} value => embedding (sourceMap value))
        (fun _ => rfl) sourceItems).symm

/-- The root pruned source compiler context embeds and then normalizes into
the exact inner context of the source root cylindrical block. -/
def LocalCylindricalFrame.sourceRetainedNormalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    WireRenaming (frame.sourceRetainedVisibleContext pair).sigs
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
  fun {_} value => frame.sourceFrameNormalization
    (frame.sourceRetainedFrameEmbedding pair value)

/-- Target counterpart of `sourceRetainedNormalization`. -/
def LocalCylindricalFrame.targetRetainedNormalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    WireRenaming (frame.targetRetainedVisibleContext pair).sigs
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
  fun {_} value => frame.targetFrameNormalization
    (frame.targetRetainedFrameEmbedding sourceArguments newArgument result
      accepted pair value)

/-- The retained root prefix is already an exact leaf receipt in the
independently normalized source and target contexts. -/
theorem LocalCylindricalFrame.rootRetainedItems_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame) :
    ∃ (sourceItems : ItemSeq definitions
          (frame.sourceRetainedVisibleContext pair).sigs)
      (targetItems : ItemSeq definitions
          (frame.targetRetainedVisibleContext pair).sigs),
      ConcreteElaboration.compileNodes? definitions source.val
          (frame.sourceRetainedVisibleContext pair)
          ((source.val.nodesAt (source.val.wires wire).scope).filter
            (fun node => decide (node ∉ argumentSiteNodes result.sites))) =
        some sourceItems ∧
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (frame.targetRetainedVisibleContext pair)
          (((replacementBase result.plan).nodesAt
              (retainedRegion source (source.val.wires wire).scope)).map
            (fun retained => ConcreteWireQuantifier.Internal.checkedNode
              result.generated
              (Fin.castAdd result.sites.sites.length retained))) =
        some targetItems ∧
      targetItems.renameWires
          (frame.targetRetainedNormalization sourceArguments newArgument
            result accepted pair) =
        (sourceItems.renameWires
          (frame.sourceRetainedNormalization pair)).renameWires
            ((frame.rootBounds sourceArguments sourceSignature newArgument
              result accepted).embed (fun {_} value => value)) := by
  obtain ⟨sourceItems, targetItems, sourceCompiled, targetCompiled,
      targetExact⟩ :=
    frame.compileRetainedNodePrefixPair?_complete sourceArguments newArgument
      result accepted pair
  refine ⟨sourceItems, targetItems, sourceCompiled, targetCompiled, ?_⟩
  subst targetItems
  let retained := frame.retainedVisibleContext newArgument result accepted pair
  let sourceMap : WireRenaming
      (frame.sourceRetainedVisibleContext pair).sigs
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
    fun {_} value => frame.sourceRetainedNormalization pair value
  let targetMap : WireRenaming
      (frame.targetRetainedVisibleContext pair).sigs
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
    fun {_} value => frame.targetRetainedNormalization sourceArguments
      newArgument result accepted pair value
  let embedding : WireRenaming
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter))
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
    (frame.rootBounds sourceArguments sourceSignature newArgument result
      accepted).embed (fun {_} value => value)
  have commutes : ∀ {signature : Sig}
      (value : Var (frame.sourceRetainedVisibleContext pair).sigs signature),
      embedding (sourceMap value) =
        targetMap (retained.wireRenaming value) := by
    intro signature value
    change
      (frame.rootBounds sourceArguments sourceSignature newArgument result
        accepted).embed (fun {_} selected => selected)
          (frame.sourceFrameNormalization
            (frame.sourceRetainedFrameEmbedding pair value)) =
        frame.targetFrameNormalization
          (frame.targetRetainedFrameEmbedding sourceArguments newArgument
            result accepted pair (retained.wireRenaming value))
    apply frame.frameNormalization_commutes_of_mapped_origin sourceArguments
      sourceSignature newArgument result accepted pair
    · have sourceRetained := retained.source_retained
        (ConcreteElaboration.WireContext.origin source.val
          (frame.sourceRetainedVisibleContext pair).ids value)
        (ConcreteElaboration.Internal.origin_member source.val value)
      have sourceOrigin :
          ConcreteElaboration.WireContext.origin source.val
              frame.sourceScope.frame.visible.ids
              (frame.sourceRetainedFrameEmbedding pair value) =
            ConcreteElaboration.WireContext.origin source.val
              (frame.sourceRetainedVisibleContext pair).ids value := by
        exact InsertionCompilation.NaturalityInternal.contextEmbedding_origin
          source.val source.val
          (frame.sourceRetainedVisibleContext pair).ids
          frame.sourceScope.frame.visible.ids (fun sourceWire => sourceWire)
          (fun _ => rfl)
          (frame.sourceRetainedVisibleContext_member_frame pair) value
      intro same
      apply sourceRetained
      rw [sourceOrigin] at same
      rw [arityShift_sourceRemovedWires_exact source wire newArgument result
        accepted]
      exact List.mem_singleton.mpr same
    · have sourceOrigin :
          ConcreteElaboration.WireContext.origin source.val
              frame.sourceScope.frame.visible.ids
              (frame.sourceRetainedFrameEmbedding pair value) =
            ConcreteElaboration.WireContext.origin source.val
              (frame.sourceRetainedVisibleContext pair).ids value := by
        exact InsertionCompilation.NaturalityInternal.contextEmbedding_origin
          source.val source.val
          (frame.sourceRetainedVisibleContext pair).ids
          frame.sourceScope.frame.visible.ids (fun sourceWire => sourceWire)
          (fun _ => rfl)
          (frame.sourceRetainedVisibleContext_member_frame pair) value
      have targetOrigin :
          ConcreteElaboration.WireContext.origin result.checked.val
              frame.targetScope.frame.visible.ids
              (frame.targetRetainedFrameEmbedding sourceArguments newArgument
                result accepted pair (retained.wireRenaming value)) =
            ConcreteElaboration.WireContext.origin result.checked.val
              (frame.targetRetainedVisibleContext pair).ids
              (retained.wireRenaming value) := by
        exact InsertionCompilation.NaturalityInternal.contextEmbedding_origin
          result.checked.val result.checked.val
          (frame.targetRetainedVisibleContext pair).ids
          frame.targetScope.frame.visible.ids (fun targetWire => targetWire)
          (fun _ => rfl)
          (frame.targetRetainedVisibleContext_member_frame sourceArguments
            newArgument result accepted pair) (retained.wireRenaming value)
      rw [targetOrigin, retained.wireRenaming_origin, sourceOrigin]
  let retainedMap : WireRenaming
      (frame.sourceRetainedVisibleContext pair).sigs
      (frame.targetRetainedVisibleContext pair).sigs :=
    fun {_} value => retained.wireRenaming value
  let combined : WireRenaming
      (frame.sourceRetainedVisibleContext pair).sigs
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
    fun {_} value => targetMap (retainedMap value)
  calc
    (sourceItems.renameWires retainedMap).renameWires targetMap =
        sourceItems.renameWires combined :=
      recursiveItemSeqRename_comp retainedMap targetMap combined
        (fun _ => rfl) sourceItems
    _ = sourceItems.renameWires
        (fun {_} value => embedding (sourceMap value)) :=
      recursiveItemSeqRename_eq _ _ (by
        intro signature value
        exact (commutes value).symm) sourceItems
    _ = (sourceItems.renameWires sourceMap).renameWires embedding :=
      (recursiveItemSeqRename_comp sourceMap embedding
        (fun {_} value => embedding (sourceMap value))
        (fun _ => rfl) sourceItems).symm

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
