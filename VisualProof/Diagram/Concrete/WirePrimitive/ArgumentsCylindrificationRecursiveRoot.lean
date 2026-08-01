import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveShapes

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

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

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
