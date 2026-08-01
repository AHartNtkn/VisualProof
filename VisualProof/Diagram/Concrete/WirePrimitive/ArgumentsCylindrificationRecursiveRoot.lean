import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveShapes

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

private theorem recursiveRoot_cast_cancel
    (same : left = right)
    (value : Var right signature) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

/-- Keep a canonical local prefix fixed while independently normalizing the
inherited outer context.  This is the context action used below the changed
relation head, where no total concrete source-to-target head map exists. -/
def recursivePrefixRenaming (localPrefix : List Sig)
    (outer : WireRenaming sourceOuter targetOuter) :
    WireRenaming (localPrefix ++ sourceOuter)
      (localPrefix ++ targetOuter) :=
  match localPrefix with
  | [] => outer
  | signature :: tail =>
      WireRenaming.lift (recursivePrefixRenaming tail outer) signature

theorem recursivePrefixRenaming_appendLeft
    (localPrefix : List Sig)
    (outer : WireRenaming sourceOuter targetOuter)
    (value : Var localPrefix signature) :
    recursivePrefixRenaming localPrefix outer
        (Var.appendLeft value sourceOuter) =
      Var.appendLeft value targetOuter := by
  induction localPrefix with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there value =>
          exact congrArg Var.there (induction value)

theorem recursivePrefixRenaming_appendRight
    (localPrefix : List Sig)
    (outer : WireRenaming sourceOuter targetOuter)
    (value : Var sourceOuter signature) :
    recursivePrefixRenaming localPrefix outer
        (Var.appendRight localPrefix value) =
      Var.appendRight localPrefix (outer value) := by
  induction localPrefix with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg Var.there induction

/-- Normalize one dependent elaborator extension and then apply the selected
independent normalization to its inherited outer spine. -/
def recursiveExtendedNormalization
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (outer : WireRenaming context.sigs normalizedOuter) :
    WireRenaming (context.extend region).sigs
      (((diagram.wiresAt region).map fun wire =>
          (diagram.wires wire).sig) ++ normalizedOuter) :=
  fun {_} value =>
    recursivePrefixRenaming
      ((diagram.wiresAt region).map fun wire =>
        (diagram.wires wire).sig) outer
      (recursiveRegionNormalization context region value)

theorem recursiveExtendedNormalization_local
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (outer : WireRenaming context.sigs normalizedOuter)
    (value : Var
      ((diagram.wiresAt region).map fun wire =>
        (diagram.wires wire).sig) signature) :
    recursiveExtendedNormalization context region outer
        ((ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendLeft value context.sigs) =
      Var.appendLeft value normalizedOuter := by
  unfold recursiveExtendedNormalization recursiveRegionNormalization
  rw [recursiveRoot_cast_cancel]
  exact recursivePrefixRenaming_appendLeft _ _ _

theorem recursiveExtendedNormalization_outer
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (outer : WireRenaming context.sigs normalizedOuter)
    (value : Var context.sigs signature) :
    recursiveExtendedNormalization context region outer
        ((ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
          Var.appendRight
            ((diagram.wiresAt region).map fun wire =>
              (diagram.wires wire).sig) value) =
      Var.appendRight
        ((diagram.wiresAt region).map fun wire =>
          (diagram.wires wire).sig) (outer value) := by
  unfold recursiveExtendedNormalization recursiveRegionNormalization
  rw [recursiveRoot_cast_cancel]
  exact recursivePrefixRenaming_appendRight _ _ _

/-- A head-excluding correspondence between independently normalized concrete
contexts.  It records exactly the relation needed by retained leaves, hole
tuples, and recursive children; the changed relation head is intentionally
outside its domain law. -/
structure RecursiveNormalizationCorrespondence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (normalizedSource normalizedTarget : List Sig) where
  sourceMap : WireRenaming sourceContext.sigs normalizedSource
  targetMap : WireRenaming targetContext.sigs normalizedTarget
  embedding : WireRenaming normalizedSource normalizedTarget
  commutes : ∀ {signature : Sig}
      (sourceValue : Var sourceContext.sigs signature)
      (targetValue : Var targetContext.sigs signature),
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        sourceValue ≠ wire →
    ConcreteElaboration.WireContext.origin result.checked.val
        targetContext.ids targetValue =
      result.contextWireMap
        (ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          sourceValue) →
    embedding (sourceMap sourceValue) = targetMap targetValue

/-- The checked root frame supplies the initial head-excluding context
correspondence used by every proper descendant. -/
def LocalCylindricalFrame.rootNormalizationCorrespondence
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
    RecursiveNormalizationCorrespondence result
      frame.sourceScope.frame.visible frame.targetScope.frame.visible
      (frame.sourceReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter))
      (frame.targetReduced ++
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)) :=
  { sourceMap := frame.sourceFrameNormalization
    targetMap := frame.targetFrameNormalization
    embedding :=
      (frame.rootBounds sourceArguments sourceSignature newArgument result
        accepted).embed (fun {_} value => value)
    commutes := fun sourceValue targetValue sourceNotHead mappedOrigin =>
      frame.frameNormalization_commutes_of_mapped_origin sourceArguments
        sourceSignature newArgument result accepted pair sourceValue
        targetValue sourceNotHead mappedOrigin }

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

/-- Root source abstraction removes exactly the exhaustive acted
applications and leaves the normalized retained prefix. -/
theorem LocalCylindricalFrame.rootSourceOrdinary_eq_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (result : ArgumentResult source wire)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (nodes retained : ItemSeq definitions
      frame.sourceScope.frame.visible.sigs)
    (nodesCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          frame.sourceScope.frame.visible
          (source.val.nodesAt (source.val.wires wire).scope) = some nodes)
    (retainedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          frame.sourceScope.frame.visible
          ((source.val.nodesAt (source.val.wires wire).scope).filter
            (fun node => decide (node ∉ argumentSiteNodes result.sites))) =
        some retained) :
    recursiveOrdinary
        (UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.sourceReduced localSourceHead)
          (nodes.renameWires frame.sourceFrameNormalization)) =
      recursiveLeafItems
        (retained.renameWires frame.sourceFrameNormalization) := by
  rw [recursiveOrdinary_abstractAppliedItems]
  apply recursiveAbstractOrdinaryItems_compileFilter definitions source.val
    frame.sourceScope.frame.visible frame.sourceFrameNormalization
    (Var.appendRight frame.sourceReduced localSourceHead)
    (argumentSiteNodes result.sites)
    (source.val.nodesAt (source.val.wires wire).scope) nodes retained
    nodesCompiled
  · simpa only [decide_not] using retainedCompiled
  · intro node nodeAt
    exact frame.sourceClassifier_isSome sourceArguments sourceSignature result
      pair node nodeAt

/-- Root target abstraction removes exactly the generated target application
sites and leaves the checked retained prefix. -/
theorem LocalCylindricalFrame.rootTargetOrdinary_eq_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (frame : LocalCylindricalFrame result sourceArguments)
    (pair : result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame)
    (nodes retained : ItemSeq definitions
      frame.targetScope.frame.visible.sigs)
    (nodesCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          frame.targetScope.frame.visible
          (result.checked.val.nodesAt
            (result.checked.val.wires result.targetWire).scope) = some nodes)
    (retainedCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          frame.targetScope.frame.visible
          (((replacementBase result.plan).nodesAt
              (retainedRegion source (source.val.wires wire).scope)).map
            (fun retained => ConcreteWireQuantifier.Internal.checkedNode
              result.generated
              (Fin.castAdd result.sites.sites.length retained))) =
        some retained) :
    recursiveOrdinary
        (UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.targetReduced localTargetHead)
          (nodes.renameWires frame.targetFrameNormalization)) =
      recursiveLeafItems
        (retained.renameWires frame.targetFrameNormalization) := by
  rw [recursiveOrdinary_abstractAppliedItems]
  apply recursiveAbstractOrdinaryItems_compileFilter definitions
    result.checked.val frame.targetScope.frame.visible
    frame.targetFrameNormalization
    (Var.appendRight frame.targetReduced localTargetHead)
    (argumentSiteNodes result.targetSites)
    (result.checked.val.nodesAt
      (result.checked.val.wires result.targetWire).scope) nodes retained
    nodesCompiled
  · have retainedNodesExact :
        (result.checked.val.nodesAt
          (result.checked.val.wires result.targetWire).scope).filter
            (fun node => !decide
              (node ∈ argumentSiteNodes result.targetSites)) =
          ((replacementBase result.plan).nodesAt
              (retainedRegion source (source.val.wires wire).scope)).map
            (fun retained => ConcreteWireQuantifier.Internal.checkedNode
              result.generated
              (Fin.castAdd result.sites.sites.length retained)) := by
      calc
        _ = (result.checked.val.nodesAt
              (result.regionImage (source.val.wires wire).scope)).filter
                (fun node => !decide
                  (node ∈ argumentSiteNodes result.targetSites)) :=
          congrArg (fun region =>
            (result.checked.val.nodesAt region).filter fun node => !decide
              (node ∈ argumentSiteNodes result.targetSites))
              result.targetWire_scope_regionImage
        _ = _ := ArgumentResult.targetRetainedNodesAt_exact result
          (source.val.wires wire).scope
    rw [retainedNodesExact]
    exact retainedCompiled
  · intro node nodeAt
    exact frame.targetClassifier_isSome result pair node nodeAt

/-- Ordered child compilations can be paired after independent source and
target normalization.  Unlike `recursiveChildrenReceipts`, this theorem does
not require a concrete action across the changed relation head. -/
theorem recursiveNormalizedChildrenReceipts
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (sourceMap : WireRenaming sourceContext.sigs normalizedSource)
    (targetMap : WireRenaming targetContext.sigs normalizedTarget)
    (embedding : WireRenaming normalizedSource normalizedTarget)
    (sourceHead : Var normalizedSource (.rel smallerArguments))
    (targetHead : Var normalizedTarget (.rel largerArguments))
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
      Option (Region definitions context.sigs))
    (targetRecurse : (region : result.checked.val.RegionId) →
      (context : ConcreteElaboration.WireContext result.checked.val) →
      Option (Region definitions context.sigs))
    (children : List source.val.RegionId)
    (buildChild : ∀ (child : source.val.RegionId)
      (sourceBody : Region definitions sourceContext.sigs)
      (targetBody : Region definitions targetContext.sigs),
      child ∈ children →
      sourceRecurse child sourceContext = some sourceBody →
      targetRecurse (result.regionEquiv child) targetContext =
        some targetBody →
      ∃ shape : CylindricalShape definitions insertion
          normalizedSource normalizedTarget,
        shape.consistent ∧
        (∀ {signature : Sig} (value : Var normalizedSource signature),
          shape.embedding value = embedding value) ∧
        shape.smaller = UniformIntrinsicRegion.abstractApplied
          sourceHead (sourceBody.renameWires sourceMap) ∧
        shape.larger = UniformIntrinsicRegion.abstractApplied
          targetHead (targetBody.renameWires targetMap)) :
    ∀ (sourceItems : ItemSeq definitions sourceContext.sigs)
      (targetItems : ItemSeq definitions targetContext.sigs),
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext children = some sourceItems →
      ConcreteElaboration.compileChildrenWith? definitions result.checked.val
          targetRecurse targetContext (children.map result.regionEquiv) =
        some targetItems →
      ∃ shapes : List (CylindricalShape definitions insertion
          normalizedSource normalizedTarget),
        (∀ shape, shape ∈ shapes → shape.consistent ∧
          ∀ {signature : Sig} (value : Var normalizedSource signature),
            shape.embedding value = embedding value) ∧
        UniformIntrinsicRegion.abstractAppliedItems sourceHead
            (sourceItems.renameWires sourceMap) =
          .mk (recursiveChildSmallerItems insertion shapes) ⟨[]⟩ ∧
        UniformIntrinsicRegion.abstractAppliedItems targetHead
            (targetItems.renameWires targetMap) =
          .mk (recursiveChildLargerItems insertion shapes) ⟨[]⟩ := by
  intro sourceItems targetItems sourceCompiled targetCompiled
  induction children generalizing sourceItems targetItems with
  | nil =>
      simp [ConcreteElaboration.compileChildrenWith?] at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      exact ⟨[], by simp, rfl, rfl⟩
  | cons child tail induction =>
      obtain ⟨sourceBody, sourceRest, sourceBodyCompiled,
          sourceRestCompiled, sourceItemsExact⟩ :=
        recursiveCompileChildrenCons definitions source.val sourceRecurse
          sourceContext child tail sourceItems sourceCompiled
      obtain ⟨targetBody, targetRest, targetBodyCompiled,
          targetRestCompiled, targetItemsExact⟩ :=
        recursiveCompileChildrenCons definitions result.checked.val
          targetRecurse targetContext (result.regionEquiv child)
          (tail.map result.regionEquiv) targetItems (by
            simpa using targetCompiled)
      obtain ⟨childShape, childConsistent, childEmbedding, childSmaller,
          childLarger⟩ :=
        buildChild child sourceBody targetBody (by simp)
          sourceBodyCompiled targetBodyCompiled
      obtain ⟨tailShapes, tailValid, tailSmaller, tailLarger⟩ :=
        induction
          (fun candidate candidateSource candidateTarget member =>
            buildChild candidate candidateSource candidateTarget
              (List.mem_cons_of_mem child member))
          sourceRest targetRest sourceRestCompiled targetRestCompiled
      refine ⟨childShape :: tailShapes, ?_, ?_, ?_⟩
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with rfl | tailMember
        · exact ⟨childConsistent, childEmbedding⟩
        · exact tailValid candidate tailMember
      · subst sourceItems
        simp only [ItemSeq.renameWires, Item.renameWires,
          UniformIntrinsicRegion.abstractAppliedItems,
          recursiveChildSmallerItems]
        rw [← childSmaller, tailSmaller]
        rfl
      · subst targetItems
        simp only [ItemSeq.renameWires, Item.renameWires,
          UniformIntrinsicRegion.abstractAppliedItems,
          recursiveChildLargerItems]
        rw [← childLarger, tailLarger]
        rfl

/-- Once ordered child compilations have been lifted to normalized recursive
cut receipts, the retained root leaves and exact root holes assemble the
complete identity-outer cylindrical shape. -/
theorem LocalCylindricalFrame.rootCylindricalShape_of_children
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
      frame.sourceScope.frame frame.targetScope.frame)
    (buildChildren : ∀ (fuel : Nat)
      (sourceChildren : ItemSeq definitions
        frame.sourceScope.frame.visible.sigs)
      (targetChildren : ItemSeq definitions
        frame.targetScope.frame.visible.sigs),
      ConcreteElaboration.compileChildrenWith? definitions source.val
          (ConcreteElaboration.compileRegion? definitions source.val
            fuel)
          frame.sourceScope.frame.visible
          (source.val.childrenOf (source.val.wires wire).scope) =
        some sourceChildren →
      ConcreteElaboration.compileChildrenWith? definitions result.checked.val
          (ConcreteElaboration.compileRegion? definitions result.checked.val
            fuel)
          frame.targetScope.frame.visible
          (result.checked.val.childrenOf
            (result.checked.val.wires result.targetWire).scope) =
        some targetChildren →
      ∃ shapes : List (CylindricalShape definitions
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted)
          (frame.sourceReduced ++
            ((.rel sourceArguments) :: (.rel result.targetArguments) ::
              frame.context.siteOuter))
          (frame.targetReduced ++
            ((.rel sourceArguments) :: (.rel result.targetArguments) ::
              frame.context.siteOuter))),
        (∀ shape, shape ∈ shapes → shape.consistent ∧
          ∀ {signature : Sig}
            (value : Var
              (frame.sourceReduced ++
                ((.rel sourceArguments) :: (.rel result.targetArguments) ::
                  frame.context.siteOuter)) signature),
            shape.embedding value =
              (frame.rootBounds sourceArguments sourceSignature newArgument
                result accepted).embed (fun {_} selected => selected) value) ∧
        UniformIntrinsicRegion.abstractAppliedItems
            (Var.appendRight frame.sourceReduced localSourceHead)
            (sourceChildren.renameWires frame.sourceFrameNormalization) =
          .mk (recursiveChildSmallerItems
            (arityShiftInsertion source wire sourceArguments sourceSignature
              newArgument result accepted) shapes) ⟨[]⟩ ∧
        UniformIntrinsicRegion.abstractAppliedItems
            (Var.appendRight frame.targetReduced localTargetHead)
            (targetChildren.renameWires frame.targetFrameNormalization) =
          .mk (recursiveChildLargerItems
            (arityShiftInsertion source wire sourceArguments sourceSignature
              newArgument result accepted) shapes) ⟨[]⟩) :
    ∃ shape : CylindricalShape definitions
        (arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted)
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter)
        ((.rel sourceArguments) :: (.rel result.targetArguments) ::
          frame.context.siteOuter),
      shape.consistent ∧
      (∀ {signature : Sig}
        (value : Var
          ((.rel sourceArguments) :: (.rel result.targetArguments) ::
            frame.context.siteOuter) signature),
        shape.embedding value = value) ∧
      shape.smaller = frame.sourceShape ∧
      shape.larger = frame.targetShape := by
  obtain ⟨sourceFuel, sourceNodes, sourceChildren, sourceNodesCompiled,
      sourceChildrenCompiled, sourceBodyExact⟩ :=
    frame.sourceScope.siteBody_decomposition
  obtain ⟨targetFuel, targetNodes, targetChildren, targetNodesCompiled,
      targetChildrenCompiled, targetBodyExact⟩ :=
    frame.targetScope.siteBody_decomposition
  let commonFuel := max sourceFuel targetFuel
  have sourceChildrenLifted := recursiveCompileChildren_fuel_mono definitions
    source.val sourceFuel commonFuel (Nat.le_max_left _ _)
    frame.sourceScope.frame.visible
    (source.val.childrenOf (source.val.wires wire).scope) sourceChildren
    sourceChildrenCompiled
  have targetChildrenLifted := recursiveCompileChildren_fuel_mono definitions
    result.checked.val targetFuel commonFuel (Nat.le_max_right _ _)
    frame.targetScope.frame.visible
    (result.checked.val.childrenOf
      (result.checked.val.wires result.targetWire).scope) targetChildren
    targetChildrenCompiled
  obtain ⟨childShapes, childShapesValid, sourceChildrenExact,
      targetChildrenExact⟩ :=
    buildChildren commonFuel sourceChildren targetChildren sourceChildrenLifted
      targetChildrenLifted
  obtain ⟨sourcePruned, targetPruned, sourceFrameItems, targetFrameItems,
      sourcePrunedCompiled, targetPrunedCompiled, sourceFrameCompiled,
      targetFrameCompiled, sourceFrameExact, targetFrameExact,
      targetPrunedExact⟩ :=
    frame.compileRetainedNodePrefixFramePair?_complete sourceArguments
      newArgument result accepted pair
  have sourceOrdinary := frame.rootSourceOrdinary_eq_retained
    sourceArguments sourceSignature result pair sourceNodes sourceFrameItems
    sourceNodesCompiled sourceFrameCompiled
  have targetOrdinary := frame.rootTargetOrdinary_eq_retained result pair
    targetNodes targetFrameItems targetNodesCompiled targetFrameCompiled
  have normalizedRetained := frame.rootRetainedItems_exact sourceArguments
    sourceSignature newArgument result accepted pair
  obtain ⟨sourcePruned', targetPruned', sourcePrunedCompiled',
      targetPrunedCompiled', normalizedRetainedExact⟩ := normalizedRetained
  have sourcePrunedSame : sourcePruned' = sourcePruned := by
    exact Option.some.inj (sourcePrunedCompiled'.symm.trans sourcePrunedCompiled)
  have targetPrunedSame : targetPruned' = targetPruned := by
    exact Option.some.inj (targetPrunedCompiled'.symm.trans targetPrunedCompiled)
  subst sourcePruned'
  subst targetPruned'
  let insertion := arityShiftInsertion source wire sourceArguments
    sourceSignature newArgument result accepted
  let bounds := frame.rootBounds sourceArguments sourceSignature newArgument
    result accepted
  let outer : WireRenaming
      ((.rel sourceArguments) :: (.rel result.targetArguments) ::
        frame.context.siteOuter)
      ((.rel sourceArguments) :: (.rel result.targetArguments) ::
        frame.context.siteOuter) := fun {_} value => value
  let sourceRetained := sourcePruned.renameWires
    (frame.sourceRetainedNormalization pair)
  let holes := frame.rootHoles sourceArguments sourceSignature newArgument
    result accepted pair
  let shape := recursiveBlockReceipt insertion bounds outer sourceRetained
    childShapes holes
  have shapeValid := recursiveBlockReceipt_valid insertion bounds outer
    sourceRetained childShapes childShapesValid holes
  refine ⟨shape, shapeValid.1, shapeValid.2, ?_, ?_⟩
  · rw [frame.sourceShape_compiled]
    unfold shape
    rw [recursiveBlockReceipt_smaller]
    rw [sourceBodyExact]
    simp only [Region.renameWires,
      UniformIntrinsicRegion.ItemSeq.renameWires_append]
    simp only [UniformIntrinsicRegion.abstractApplied]
    rw [UniformIntrinsicRegion.abstractAppliedItems_append]
    apply congrArg (wrapArgumentBinds frame.sourceReduced)
    cases sourceNodeShape :
        UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.sourceReduced localSourceHead)
          (sourceNodes.renameWires frame.sourceFrameNormalization) with
    | mk sourceOrdinaryItems sourceNodeHoles =>
        rw [sourceNodeShape] at sourceOrdinary
        change sourceOrdinaryItems = _ at sourceOrdinary
        rw [sourceChildrenExact]
        simp only [UniformIntrinsicRegion.appendAbstracted]
        rw [sourceOrdinary, sourceFrameExact]
        congr 1
        · rw [recursiveChildSmallerItems_eq]
          rw [recursiveItemSeqRename_comp
            (frame.sourceRetainedFrameEmbedding pair)
            frame.sourceFrameNormalization
            (frame.sourceRetainedNormalization pair)
            (fun _ => rfl) sourcePruned]
        · congr 1
          simp only [List.append_nil]
          change
            (UniformIntrinsicRegion.abstractApplied
              (Var.appendRight frame.sourceReduced localSourceHead)
              (frame.sourceScope.frame.siteBody.renameWires
                frame.sourceFrameNormalization)).holeValues =
              sourceNodeHoles.values
          rw [sourceBodyExact]
          simp only [Region.renameWires,
            UniformIntrinsicRegion.ItemSeq.renameWires_append,
            UniformIntrinsicRegion.abstractApplied]
          rw [UniformIntrinsicRegion.abstractAppliedItems_append,
            sourceNodeShape, sourceChildrenExact]
          simp [UniformIntrinsicRegion.holeValues,
            UniformIntrinsicRegion.appendAbstracted]
  · rw [frame.targetShape_compiled]
    unfold shape
    rw [recursiveBlockReceipt_larger]
    rw [targetBodyExact]
    simp only [Region.renameWires,
      UniformIntrinsicRegion.ItemSeq.renameWires_append]
    simp only [UniformIntrinsicRegion.abstractApplied]
    rw [UniformIntrinsicRegion.abstractAppliedItems_append]
    apply congrArg (wrapArgumentBinds frame.targetReduced)
    cases targetNodeShape :
        UniformIntrinsicRegion.abstractAppliedItems
          (Var.appendRight frame.targetReduced localTargetHead)
          (targetNodes.renameWires frame.targetFrameNormalization) with
    | mk targetOrdinaryItems targetNodeHoles =>
        rw [targetNodeShape] at targetOrdinary
        change targetOrdinaryItems = _ at targetOrdinary
        rw [targetChildrenExact]
        simp only [UniformIntrinsicRegion.appendAbstracted]
        rw [targetOrdinary, targetFrameExact]
        rw [recursiveItemSeqRename_comp
          (frame.targetRetainedFrameEmbedding sourceArguments newArgument
            result accepted pair)
          frame.targetFrameNormalization
          (frame.targetRetainedNormalization sourceArguments newArgument
            result accepted pair)
          (fun _ => rfl) targetPruned]
        rw [normalizedRetainedExact]
        congr 1
        · rw [recursiveChildLargerItems_eq]
        · congr 1
          simp only [List.append_nil]
          change
            (UniformIntrinsicRegion.abstractApplied
              (Var.appendRight frame.targetReduced localTargetHead)
              (frame.targetScope.frame.siteBody.renameWires
                frame.targetFrameNormalization)).holeValues =
              targetNodeHoles.values
          rw [targetBodyExact]
          simp only [Region.renameWires,
            UniformIntrinsicRegion.ItemSeq.renameWires_append,
            UniformIntrinsicRegion.abstractApplied]
          rw [UniformIntrinsicRegion.abstractAppliedItems_append,
            targetNodeShape, targetChildrenExact]
          simp [UniformIntrinsicRegion.holeValues,
            UniformIntrinsicRegion.appendAbstracted]

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
