import VisualProof.Diagram.Concrete.ElaborationTransport
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalitySupport
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsOperations

namespace VisualProof
namespace ConcreteWirePrimitive

open ConcreteElaboration
open ConcreteWireQuantifier

/-- Total carrier used by compiler contexts.  Its removed-wire branch is
unobservable: retained-context receipts prove every visible id takes the
canonical retained-image branch. -/
def ArgumentResult.contextWireMap
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId) : result.checked.val.WireId :=
  if retained : sourceWire ∉ result.sourceRemovedWires then
    result.retainedWireImage sourceWire retained
  else
    result.targetWire

theorem ArgumentResult.contextWireMap_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.contextWireMap sourceWire =
      result.retainedWireImage sourceWire retained := by
  unfold ArgumentResult.contextWireMap
  rw [dif_pos retained]

theorem ArgumentResult.contextWireMap_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires (result.contextWireMap sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  rw [result.contextWireMap_retained sourceWire retained]
  exact result.retainedWireImage_signature sourceWire retained

/-- A wire local to a strict ancestor of a localized replacement cannot be
among the replacement's removed wires. -/
theorem ArgumentResult.wireAt_strictlyAbove_not_removed
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope)
    (sourceWire : source.val.WireId)
    (member : sourceWire ∈ source.val.wiresAt outer) :
    sourceWire ∉ result.sourceRemovedWires := by
  intro removed
  rw [ConcreteDiagram.wiresAt, List.mem_filter] at member
  have localScope := eq_of_beq member.2
  have actedEnclosesOuter :
      source.val.Encloses (source.val.wires wire).scope outer := by
    rw [← localScope]
    exact localized.removed_enclosed sourceWire removed
  have same := factor_encloses_antisymm definitions source.val
    source.property outerEncloses actedEnclosesOuter
  exact strict same

/-- Every incidence of a retained source node is reproduced on the
canonical target node and wire images. -/
theorem ArgumentResult.retainedNode_forwardIncident
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (node : source.val.NodeId)
    (nodeRetained : node ∉ argumentSiteNodes result.sites)
    (port : CPort)
    (sourceWire : source.val.WireId)
    (incident :
      (⟨node, port⟩ : CEndpoint source.val.nodeCount) ∈
        (source.val.wires sourceWire).endpoints) :
    (⟨result.retainedNodeImage node nodeRetained, port⟩ :
        CEndpoint result.checked.val.nodeCount) ∈
      (result.checked.val.wires
        (result.contextWireMap sourceWire)).endpoints := by
  have required := ConcreteDiagram.incident_port_required definitions
    source.val source.property sourceWire ⟨node, port⟩ incident
  have sourceOwner := ConcreteDiagram.endpointOwner?_eq_of_incident
    definitions source.val source.property node port required sourceWire
    incident
  have sourceWireRetained := result.ownerOfRetainedNode_not_removed node
    nodeRetained port sourceWire sourceOwner
  have targetOwner := result.retainedNodeImage_endpointOwner node
    nodeRetained port required sourceWire sourceOwner
  rw [result.contextWireMap_retained sourceWire sourceWireRetained]
  exact ConcreteDiagram.endpointOwner?_incident result.checked.val
    ⟨result.retainedNodeImage node nodeRetained, port⟩
    (result.retainedWireImage sourceWire sourceWireRetained) targetOwner

/-- At a strict ancestor of the acted scope, ordered local wire identifiers
are exactly the canonical images of the source identifiers. -/
theorem ArgumentResult.wiresAt_contextWireMap_strictlyAbove
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope) :
    result.checked.val.wiresAt (result.regionImage outer) =
      (source.val.wiresAt outer).map result.contextWireMap := by
  rw [result.wiresAt_decomposition outer]
  have retainedFilter :
      (source.val.wiresAt outer).filter
          (fun sourceWire =>
            decide (sourceWire ∉ result.sourceRemovedWires)) =
        source.val.wiresAt outer := by
    apply List.filter_eq_self.mpr
    intro sourceWire member
    exact decide_eq_true
      (result.wireAt_strictlyAbove_not_removed localized outer
        outerEncloses strict sourceWire member)
  have headEmpty :
      (Data.Finite.allFin 1).filter (fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source outer) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro _head _member accepted
    apply strict
    apply (Internal.noRegionRemovalEquiv source).injective
    rw [← retainedRegion_eq_noRegionRemovalEquiv,
      ← retainedRegion_eq_noRegionRemovalEquiv]
    exact (eq_of_beq accepted).symm
  have localEmpty :
      (Data.Finite.allFin result.spec.localCount).filter (fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source outer) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro fresh _member accepted
    have localExact : result.spec.localScope fresh = outer := by
      apply (Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact eq_of_beq accepted
    have actedEnclosesOuter :
        source.val.Encloses (source.val.wires wire).scope outer := by
      rw [← localExact]
      exact localized.local_enclosed fresh
    have same := factor_encloses_antisymm definitions source.val
      source.property outerEncloses actedEnclosesOuter
    exact strict same
  rw [headEmpty, localEmpty]
  simp only [List.map_nil, List.append_nil]
  have baseSources := batchRemovalCandidate_wiresAt_sources
    result.plan.removal outer
  rw [← retainedRegion_eq_noRegionRemovalEquiv] at baseSources
  change
    ((replacementBase result.plan).wiresAt
        (retainedRegion source outer)).map
          (Internal.sourceRetainedWire source result.sourceRemovedWires) =
      (source.val.wiresAt outer).filter
        (fun sourceWire =>
          decide (sourceWire ∉ result.sourceRemovedWires)) at baseSources
  rw [retainedFilter] at baseSources
  calc
    _ = ((replacementBase result.plan).wiresAt
          (retainedRegion source outer)).map (fun retained =>
            result.contextWireMap
              (Internal.sourceRetainedWire source
                result.sourceRemovedWires retained)) := by
        apply List.map_congr_left
        intro retained _member
        have sourceRetained :
            Internal.sourceRetainedWire source result.sourceRemovedWires
                retained ∉ result.sourceRemovedWires := by
          have member := List.get_mem
            (Internal.retainedWires source result.sourceRemovedWires) retained
          exact of_decide_eq_true (List.mem_filter.mp member).2
        rw [result.contextWireMap_retained _ sourceRetained]
        unfold ArgumentResult.retainedWireImage
        apply congrArg (Internal.checkedWire result.generated)
        exact congrArg (Fin.castAdd (1 + result.spec.localCount))
          (Internal.retainedWireIndex_sourceRetainedWire source
            result.sourceRemovedWires retained).symm
    _ = (((replacementBase result.plan).wiresAt
          (retainedRegion source outer)).map
            (Internal.sourceRetainedWire source
              result.sourceRemovedWires)).map result.contextWireMap := by
        rw [List.map_map]
        apply List.map_congr_left
        intro retained _member
        rfl
    _ = _ := by rw [baseSources]

private def contextEmbeddingVisible
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount) :
    (sourceIds : List source.WireId) →
    (targetIds : List target.WireId) →
    (mapWire : source.WireId → target.WireId) →
    (signature : ∀ wire, wire ∈ sourceIds →
      (target.wires (mapWire wire)).sig = (source.wires wire).sig) →
    (visible : ∀ wire, wire ∈ sourceIds → mapWire wire ∈ targetIds) →
    WireRenaming
      (sourceIds.map fun wire => (source.wires wire).sig)
      (targetIds.map fun wire => (target.wires wire).sig)
  | [], _, _, _, _ => fun value => nomatch value
  | head :: tail, targetIds, mapWire, signature, visible =>
      fun value =>
        match value with
        | .here =>
            InsertionCompilation.NaturalityInternal.castVar
              (signature head (by simp))
              (InsertionCompilation.NaturalityInternal.varForMember target
                targetIds (mapWire head) (visible head (by simp)))
        | .there rest =>
            contextEmbeddingVisible source target tail targetIds mapWire
              (fun wire member => signature wire
                (List.mem_cons_of_mem head member))
              (fun wire member => visible wire
                (List.mem_cons_of_mem head member)) rest

private theorem contextEmbeddingVisible_origin
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount)
    (sourceIds : List source.WireId)
    (targetIds : List target.WireId)
    (mapWire : source.WireId → target.WireId)
    (signature : ∀ wire, wire ∈ sourceIds →
      (target.wires (mapWire wire)).sig = (source.wires wire).sig)
    (visible : ∀ wire, wire ∈ sourceIds → mapWire wire ∈ targetIds)
    {sig : Sig}
    (value : Var (sourceIds.map fun wire => (source.wires wire).sig) sig) :
    WireContext.origin target targetIds
        (contextEmbeddingVisible source target sourceIds targetIds mapWire
          signature visible value) =
      mapWire (WireContext.origin source sourceIds value) := by
  induction sourceIds with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          unfold contextEmbeddingVisible
          change
            WireContext.origin target targetIds
                (InsertionCompilation.NaturalityInternal.castVar
                  (signature head (by simp))
                  (InsertionCompilation.NaturalityInternal.varForMember target
                    targetIds (mapWire head) (visible head (by simp)))) =
              mapWire head
          rw [InsertionCompilation.NaturalityInternal.origin_castVar,
            InsertionCompilation.NaturalityInternal.varForMember_origin]
      | there rest =>
          exact induction
            (fun wire member => signature wire
              (List.mem_cons_of_mem head member))
            (fun wire member => visible wire
              (List.mem_cons_of_mem head member)) rest

/-- Context-local correspondence used above an argument replacement.  The
wire action is intentionally constrained only on the visible source ids:
arity replacement has no signature-preserving action on removed wires. -/
structure ArgumentResult.RetainedContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceContext : WireContext source.val)
    (targetContext : WireContext result.checked.val) where
  source_retained :
    ∀ sourceWire, sourceWire ∈ sourceContext.ids →
      sourceWire ∉ result.sourceRemovedWires
  ids_exact :
    targetContext.ids = sourceContext.ids.map result.contextWireMap

namespace ArgumentResult.RetainedContext

/-- Empty root contexts correspond before the compiler descends through any
region. -/
def empty
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    result.RetainedContext (WireContext.empty source.val)
      (WireContext.empty result.checked.val) :=
  { ids_exact := rfl
    source_retained := by
      intro sourceWire member
      simp [WireContext.empty] at member }

theorem signature_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (sourceWire : source.val.WireId)
    (member : sourceWire ∈ sourceContext.ids) :
    (result.checked.val.wires (result.contextWireMap sourceWire)).sig =
      (source.val.wires sourceWire).sig :=
  result.contextWireMap_signature sourceWire
    (context.source_retained sourceWire member)

/-- Descending through a strict ancestor extends both compiler contexts by
the corresponding ordered local-wire blocks. -/
def extendStrictlyAbove
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope) :
    result.RetainedContext (sourceContext.extend outer)
      (targetContext.extend (result.regionImage outer)) :=
  { source_retained := by
      intro sourceWire member
      simp only [WireContext.extend, List.mem_append] at member
      rcases member with localMember | previous
      · exact result.wireAt_strictlyAbove_not_removed localized outer
          outerEncloses strict sourceWire localMember
      · exact context.source_retained sourceWire previous
    ids_exact := by
      unfold WireContext.extend
      rw [result.wiresAt_contextWireMap_strictlyAbove localized outer
        outerEncloses strict, context.ids_exact, List.map_append] }

/-- Corresponding visible contexts have definitionally ordered equal
signature lists, even though their concrete wire identifiers differ. -/
theorem sigs_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext) :
    targetContext.sigs = sourceContext.sigs := by
  unfold WireContext.sigs
  rw [context.ids_exact, List.map_map]
  apply List.map_congr_left
  intro sourceWire member
  exact context.signature_exact sourceWire member

/-- Rename typed variables from a source visible context to its retained
target context. -/
def wireRenaming
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext) :
    WireRenaming sourceContext.sigs targetContext.sigs :=
  contextEmbeddingVisible source.val result.checked.val sourceContext.ids
    targetContext.ids result.contextWireMap context.signature_exact (by
      intro sourceWire member
      rw [context.ids_exact]
      exact List.mem_map.mpr ⟨sourceWire, member, rfl⟩)

/-- The retained-context renaming acts on concrete origins by the recorded
wire map. -/
theorem wireRenaming_origin
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    WireContext.origin result.checked.val targetContext.ids
        (context.wireRenaming value) =
      result.contextWireMap
        (WireContext.origin source.val sourceContext.ids value) := by
  exact contextEmbeddingVisible_origin source.val result.checked.val
    sourceContext.ids targetContext.ids result.contextWireMap
    context.signature_exact (by
      intro sourceWire member
      rw [context.ids_exact]
      exact List.mem_map.mpr ⟨sourceWire, member, rfl⟩) value

/-- One retained source node compiles to the renamed target item under
corresponding visible contexts. -/
theorem compileNode_natural
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (sourceNode : source.val.NodeId)
    (nodeRetained : sourceNode ∉ argumentSiteNodes result.sites)
    (sourceItem : Item definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.Internal.compileNode? definitions source.val
          sourceContext sourceNode = some sourceItem) :
    ConcreteElaboration.Internal.compileNode? definitions result.checked.val
        targetContext (result.retainedNodeImage sourceNode nodeRetained) =
      some (sourceItem.renameWires context.wireRenaming) := by
  exact ConcreteElaboration.compileNode?_natural
    (leftNode := sourceNode)
    (rightNode := result.retainedNodeImage sourceNode nodeRetained)
    result.checked.property targetNodup context.wireRenaming
    result.contextWireMap context.wireRenaming_origin result.regionEquiv
    (by
      rw [result.retainedNodeImage_data sourceNode nodeRetained]
      cases source.val.nodes sourceNode <;> rfl)
    (by
      intro port sourceWire incident
      exact result.retainedNode_forwardIncident sourceNode nodeRetained port
        sourceWire incident)
    sourceCompiled

/-- Pointwise ordered correspondence between retained source nodes and their
canonical checked images. -/
inductive RetainedNodeList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List source.val.NodeId → List result.checked.val.NodeId → Type
  | nil : RetainedNodeList result [] []
  | cons
      (sourceNode : source.val.NodeId)
      (retained : sourceNode ∉ argumentSiteNodes result.sites)
      (tail : RetainedNodeList result sourceTail targetTail) :
      RetainedNodeList result (sourceNode :: sourceTail)
        (result.retainedNodeImage sourceNode retained :: targetTail)

/-- Ordered retained node sequences compile by pointwise renaming. -/
theorem compileNodes_natural
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    {sourceNodes : List source.val.NodeId}
    {targetNodes : List result.checked.val.NodeId}
    (nodes : RetainedNodeList result sourceNodes targetNodes)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      compileNodes? definitions source.val sourceContext sourceNodes =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      compileNodes? definitions result.checked.val targetContext targetNodes =
          some targetItems ∧
        targetItems = sourceItems.renameWires context.wireRenaming := by
  induction nodes generalizing sourceItems with
  | nil =>
      simp only [compileNodes?, Option.some.injEq] at sourceCompiled ⊢
      subst sourceItems
      exact ⟨.nil, rfl, rfl⟩
  | @cons sourceTail targetTail sourceNode retained tail induction =>
      simp only [compileNodes?] at sourceCompiled ⊢
      cases sourceHeadEquation :
          ConcreteElaboration.Internal.compileNode? definitions source.val
            sourceContext sourceNode with
      | none => simp [sourceHeadEquation] at sourceCompiled
      | some sourceHead =>
          cases sourceTailEquation :
              compileNodes? definitions source.val sourceContext sourceTail with
          | none => simp [sourceHeadEquation, sourceTailEquation] at sourceCompiled
          | some sourceRest =>
              have sourceItemsExact :
                  sourceItems = .cons sourceHead sourceRest := by
                exact (Option.some.inj (by
                  simpa [sourceHeadEquation, sourceTailEquation] using
                    sourceCompiled)).symm
              subst sourceItems
              have targetHeadEquation := context.compileNode_natural
                targetNodup sourceNode retained sourceHead sourceHeadEquation
              obtain ⟨targetRest, targetTailEquation, targetRestExact⟩ :=
                induction sourceTailEquation
              refine ⟨.cons (sourceHead.renameWires context.wireRenaming)
                targetRest, ?_, ?_⟩
              · simp [targetHeadEquation, targetTailEquation]
              · simp [ItemSeq.renameWires, targetRestExact]

end ArgumentResult.RetainedContext

end ConcreteWirePrimitive
end VisualProof
