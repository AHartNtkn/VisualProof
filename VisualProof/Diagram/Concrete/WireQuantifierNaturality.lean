import VisualProof.Diagram.Concrete.WireQuantifierIota
import VisualProof.Diagram.Concrete.Subgraph.FactorizationSemantics

namespace VisualProof

universe u

/-!
Compiler naturality for the concrete wire-quantifier owner.

This Task-8-only helper owns the typed non-injective wire quotient and compiler
transport. It contains no rule policy, relation reification, or public applied
receipt.
-/

namespace ConcreteWireQuantifier

namespace IotaJoinSemantics

/-- The non-injective wire quotient: the deleted inner wire maps to the outer. -/
private def targetWire
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : source.val.WireId) :
    result.checked.val.WireId :=
  if survives : wire ≠ inner then
    result.wireImage wire survives
  else
    result.outerWire

/-- Pull a checked target region back through the count-preserving region map. -/
def sourceRegion
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (region : result.checked.val.RegionId) :
    source.val.RegionId :=
  Fin.cast result.regionCount region

@[simp] theorem regionImage_sourceRegion
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (region : result.checked.val.RegionId) :
    result.regionImage (sourceRegion result region) = region := by
  apply Fin.ext
  rfl

@[simp] private theorem sourceRegion_regionImage
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (region : source.val.RegionId) :
    sourceRegion result (result.regionImage region) = region := by
  apply Fin.ext
  rfl

/--
The retained source representative of one checked join-output wire.

This is the section of the non-injective source-to-target wire map used by the
compiler proof.  The deleted inner wire is absent from the dense retained
list, so every representative supplied by this section survives.
-/
private def sourceWire
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : result.checked.val.WireId) :
    source.val.WireId :=
  (source.val.wiresList.filter fun candidate =>
    decide (candidate ≠ inner)).get
    (Fin.cast result.wireCount wire)

private theorem sourceWire_survives
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : result.checked.val.WireId) :
    sourceWire result wire ≠ inner := by
  have member :
      sourceWire result wire ∈
        source.val.wiresList.filter fun candidate =>
          decide (candidate ≠ inner) :=
    List.get_mem _ _
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- The checked join wire map is split-surjective on retained wires. -/
private theorem wireImage_sourceWire
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : result.checked.val.WireId) :
    result.wireImage (sourceWire result wire)
        (sourceWire_survives result wire) =
      wire := by
  unfold IotaJoinResult.wireImage sourceWire
  apply Fin.ext
  change
    (DenseList.index
      (source.val.wiresList.filter fun candidate =>
        decide (candidate ≠ inner))
      ((source.val.wiresList.filter fun candidate =>
        decide (candidate ≠ inner)).get
          (Fin.cast result.wireCount wire)) _).val =
      wire.val
  rw [DenseList.index_get
    (source.val.wiresList.filter fun candidate =>
      decide (candidate ≠ inner))
    ((Data.Finite.allFin_nodup source.val.wireCount).filter _)
    (Fin.cast result.wireCount wire)]
  rfl

@[simp] private theorem targetWire_sourceWire
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : result.checked.val.WireId) :
    targetWire result (sourceWire result wire) = wire := by
  rw [targetWire, dif_pos (sourceWire_survives result wire)]
  exact wireImage_sourceWire result wire

@[simp] private theorem sourceWire_wireImage
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : source.val.WireId)
    (survives : wire ≠ inner) :
    sourceWire result (result.wireImage wire survives) = wire := by
  have member :
      wire ∈
        source.val.wiresList.filter fun candidate =>
          decide (candidate ≠ inner) := by
    simp [ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, survives]
  unfold sourceWire IotaJoinResult.wireImage
  apply Fin.ext
  change
    ((source.val.wiresList.filter fun candidate =>
      decide (candidate ≠ inner)).get
        (DenseList.index
          (source.val.wiresList.filter fun candidate =>
            decide (candidate ≠ inner))
          wire member)).val =
      wire.val
  rw [DenseList.get_index]

private theorem sourceWire_targetWire_of_survives
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : source.val.WireId)
    (survives : wire ≠ inner) :
    sourceWire result (targetWire result wire) = wire := by
  rw [targetWire, dif_pos survives,
    sourceWire_wireImage result wire survives]

@[simp] private theorem targetWire_signature
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : source.val.WireId) :
    (result.checked.val.wires (targetWire result wire)).sig =
      (source.val.wires wire).sig := by
  by_cases survives : wire ≠ inner
  · simp [targetWire, survives]
  · have same : wire = inner := by simpa using survives
    subst wire
    rw [targetWire, dif_neg (by simp), IotaJoinResult.outerWire,
      result.wireImage_signature]
    rw [result.source_outer_signature, result.source_inner_signature]

private theorem climb_regionImage
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (steps : Nat)
    (region : source.val.RegionId) :
    result.checked.val.climb steps (result.regionImage region) =
      (source.val.climb steps region).map result.regionImage := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps induction =>
      simp only [ConcreteDiagram.climb]
      rw [result.region_generated]
      cases data : source.val.regions region with
      | sheet => rfl
      | cut parent =>
          simp only [IotaJoinResult.renameRegion]
          exact induction parent

private theorem encloses_regionImage
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {ancestor descendant : source.val.RegionId}
    (encloses : source.val.Encloses ancestor descendant) :
    result.checked.val.Encloses
      (result.regionImage ancestor) (result.regionImage descendant) := by
  unfold ConcreteDiagram.Encloses at encloses ⊢
  rw [List.any_eq_true] at encloses ⊢
  obtain ⟨steps, _, climbed⟩ := encloses
  let targetSteps : Fin (result.checked.val.regionCount + 1) :=
    Fin.cast
      (congrArg (fun count => count + 1) result.regionCount.symm)
      steps
  refine ⟨targetSteps, Data.Finite.mem_allFin targetSteps, ?_⟩
  change
    (result.checked.val.climb steps.val
      (result.regionImage descendant) ==
        some (result.regionImage ancestor)) = true
  rw [climb_regionImage, eq_of_beq climbed]
  simp

theorem climb_add
    (diagram : ConcreteDiagram definitionCount)
    (first second : Nat)
    (region : diagram.RegionId) :
    diagram.climb (first + second) region =
      (diagram.climb first region).bind (diagram.climb second) := by
  induction first generalizing region with
  | zero => simp
  | succ first induction =>
      cases regionData : diagram.regions region with
      | sheet =>
          simp [Nat.succ_add, ConcreteDiagram.climb, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, regionData, Nat.succ_add] using
            induction parent

private theorem climb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) :
    diagram.climb (steps + 1) diagram.root = none := by
  have rootData : diagram.regions diagram.root = .sheet :=
    wellFormed.root_is_sheet
  simp [ConcreteDiagram.climb, rootData]

theorem climb_to_root_unique
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

private theorem checked_reaches_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (region : diagram.RegionId) :
    ∃ steps : Fin (diagram.regionCount + 1),
      diagram.climb steps region = some diagram.root := by
  have checked :=
    (List.all_eq_true.mp wellFormed.all_regions_reach_root)
      region (Data.Finite.mem_allFin region)
  exact
    (ConcreteElaboration.encloses_iff_exists
      diagram diagram.root region).mp (of_decide_eq_true checked)

private theorem checked_encloses_trans
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {outer middle inner : diagram.RegionId}
    (outerMiddle : diagram.Encloses outer middle)
    (middleInner : diagram.Encloses middle inner) :
    diagram.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram outer middle).mp outerMiddle
  obtain ⟨middleSteps, middleClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram middle inner).mp middleInner
  obtain ⟨rootSteps, outerRoot⟩ :=
    checked_reaches_root definitions diagram wellFormed outer
  have composed :
      diagram.climb (middleSteps.val + outerSteps.val) inner =
        some outer := by
    rw [climb_add diagram middleSteps.val outerSteps.val inner,
      middleClimb]
    exact outerClimb
  have composedRoot :
      diagram.climb
          ((middleSteps.val + outerSteps.val) + rootSteps.val)
          inner =
        some diagram.root := by
    rw [climb_add diagram
      (middleSteps.val + outerSteps.val) rootSteps.val inner,
      composed]
    exact outerRoot
  obtain ⟨canonicalRootSteps, canonicalRoot⟩ :=
    checked_reaches_root definitions diagram wellFormed inner
  have sameDepth :=
    climb_to_root_unique definitions diagram wellFormed
      composedRoot canonicalRoot
  have composedBound :
      middleSteps.val + outerSteps.val < diagram.regionCount + 1 := by
    omega
  exact
    (ConcreteElaboration.encloses_iff_exists diagram outer inner).mpr
      ⟨⟨middleSteps.val + outerSteps.val, composedBound⟩, composed⟩

private theorem targetWire_scope_encloses
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (comparable :
      source.val.Encloses
        (source.val.wires outer).scope
        (source.val.wires inner).scope)
    (wire : source.val.WireId) :
    result.checked.val.Encloses
      (result.checked.val.wires (targetWire result wire)).scope
      (result.regionImage (source.val.wires wire).scope) := by
  by_cases survives : wire ≠ inner
  · rw [targetWire, dif_pos survives, result.wireImage_scope]
    exact result.checked.val.encloses_refl _
  · have same : wire = inner := by simpa using survives
    subst wire
    rw [targetWire, dif_neg (by simp), IotaJoinResult.outerWire,
      result.wireImage_scope]
    exact encloses_regionImage result comparable

@[simp] private theorem sourceWire_signature
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : result.checked.val.WireId) :
    (source.val.wires (sourceWire result wire)).sig =
      (result.checked.val.wires wire).sig := by
  have signature :=
    targetWire_signature result (sourceWire result wire)
  rw [targetWire_sourceWire] at signature
  exact signature.symm

private theorem sourceWire_scope
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (wire : result.checked.val.WireId) :
    (result.checked.val.wires wire).scope =
      result.regionImage
        (source.val.wires (sourceWire result wire)).scope := by
  have scope :=
    result.wireImage_scope (sourceWire result wire)
      (sourceWire_survives result wire)
  rw [wireImage_sourceWire] at scope
  exact scope

structure ContextsRelated
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext :
      ConcreteElaboration.WireContext result.checked.val) : Prop where
  visible :
    ∀ wire, wire ∈ sourceContext.ids →
      targetWire result wire ∈ targetContext.ids
  backward :
    ∀ wire, wire ∈ targetContext.ids →
      sourceWire result wire ∈ sourceContext.ids

theorem empty_contexts_related
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner) :
    ContextsRelated result
      (ConcreteElaboration.WireContext.empty source.val)
      (ConcreteElaboration.WireContext.empty result.checked.val) := by
  constructor
  · intro wire member
    simp [ConcreteElaboration.WireContext.empty] at member
  · intro wire member
    simp [ConcreteElaboration.WireContext.empty] at member

/--
Comparable-scope extension is the point where this proof differs from the
co-scoped identity-collapse proof: the source-local inner wire maps to the
already visible outer wire.  Target coverage, rather than local-list equality,
supplies that visibility.
-/
theorem extend_contexts_related
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (comparable :
      source.val.Encloses
        (source.val.wires outer).scope
        (source.val.wires inner).scope)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (region : source.val.RegionId)
    (targetCoverage :
      (targetContext.extend (result.regionImage region)).Covers
        (result.regionImage region)) :
    ContextsRelated result
      (sourceContext.extend region)
      (targetContext.extend (result.regionImage region)) := by
  constructor
  · intro wire member
    simp only [ConcreteElaboration.WireContext.extend,
      List.mem_append] at member ⊢
    rcases member with localMember | outerMember
    · have enclosed :
          result.checked.val.Encloses
            (result.checked.val.wires (targetWire result wire)).scope
            (result.regionImage region) := by
        have sourceScope :
            (source.val.wires wire).scope = region := by
          exact eq_of_beq (List.mem_filter.mp localMember).2
        simpa [sourceScope] using
          targetWire_scope_encloses result comparable wire
      have covered :=
        targetCoverage (targetWire result wire) enclosed
      simpa only [ConcreteElaboration.WireContext.extend,
        List.mem_append] using covered
    · exact Or.inr (related.visible wire outerMember)
  · intro wire member
    simp only [ConcreteElaboration.WireContext.extend,
      List.mem_append] at member ⊢
    rcases member with localMember | outerMember
    · apply Or.inl
      unfold ConcreteDiagram.wiresAt at localMember ⊢
      apply List.mem_filter.mpr
      constructor
      · exact Data.Finite.mem_allFin _
      · have targetScope :=
          eq_of_beq (List.mem_filter.mp localMember).2
        have scope := sourceWire_scope result wire
        rw [targetScope] at scope
        have pulled :=
          congrArg (sourceRegion result) scope
        exact beq_iff_eq.mpr (by simpa using pulled.symm)
    · exact Or.inr (related.backward wire outerMember)

def contextRenaming
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext) :
    WireRenaming sourceContext.sigs targetContext.sigs :=
  InsertionCompilation.NaturalityInternal.contextEmbedding
    source.val result.checked.val sourceContext.ids targetContext.ids
    (targetWire result) (targetWire_signature result)
    related.visible

private theorem contextRenaming_origin
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    ConcreteElaboration.WireContext.origin result.checked.val
        targetContext.ids (contextRenaming result related value) =
      targetWire result
        (ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids value) := by
  exact
    InsertionCompilation.NaturalityInternal.contextEmbedding_origin
      source.val result.checked.val sourceContext.ids targetContext.ids
      (targetWire result) (targetWire_signature result)
      related.visible value

def contextSection
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext) :
    WireRenaming targetContext.sigs sourceContext.sigs :=
  InsertionCompilation.NaturalityInternal.contextEmbedding
    result.checked.val source.val targetContext.ids sourceContext.ids
    (sourceWire result) (sourceWire_signature result)
    related.backward

private theorem contextSection_origin
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        (contextSection result related value) =
      sourceWire result
        (ConcreteElaboration.WireContext.origin result.checked.val
          targetContext.ids value) := by
  exact
    InsertionCompilation.NaturalityInternal.contextEmbedding_origin
      result.checked.val source.val targetContext.ids sourceContext.ids
      (sourceWire result) (sourceWire_signature result)
      related.backward value

private theorem targetEndpoint_incident
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (endpoint : CEndpoint source.val.nodeCount)
    (wire : source.val.WireId)
    (incident : endpoint ∈ (source.val.wires wire).endpoints) :
    result.endpointImage endpoint ∈
      (result.checked.val.wires (targetWire result wire)).endpoints := by
  by_cases survives : wire ≠ inner
  · rw [targetWire, dif_pos survives,
      result.wireImage_endpoints]
    by_cases isOuter : wire = outer
    · subst wire
      rw [if_pos rfl]
      exact List.mem_map.mpr
        ⟨endpoint, List.mem_append_left _ incident, rfl⟩
    · rw [if_neg isOuter]
      exact List.mem_map.mpr ⟨endpoint, incident, rfl⟩
  · have same : wire = inner := by simpa using survives
    subst wire
    rw [targetWire, dif_neg (by simp), IotaJoinResult.outerWire,
      result.wireImage_endpoints, if_pos rfl]
    exact List.mem_map.mpr
      ⟨endpoint, List.mem_append_right _ incident, rfl⟩

private theorem compile_singleton_natural
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (node : source.val.NodeId)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceContext [node] =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      ConcreteElaboration.compileNodes? definitions result.checked.val
          targetContext [result.nodeImage node] =
        some targetItems ∧
      targetItems =
        sourceItems.renameWires (contextRenaming result related) := by
  apply ConcreteElaboration.compileNodes?_singleton_natural
    result.checked.property targetNodup
    (contextRenaming result related) (targetWire result)
    (targetWire_signature result)
    (contextRenaming_origin result related)
    result.regionImage node (result.nodeImage node)
  · rw [result.node_generated]
    cases source.val.nodes node <;> rfl
  · intro port wire incident
    exact targetEndpoint_incident result ⟨node, port⟩ wire incident
  · exact sourceCompiled

private def sourceNode
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (node : result.checked.val.NodeId) :
    source.val.NodeId :=
  Fin.cast result.nodeCount node

@[simp] private theorem nodeImage_sourceNode
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (node : result.checked.val.NodeId) :
    result.nodeImage (sourceNode result node) = node := by
  apply Fin.ext
  rfl

@[simp] private theorem sourceNode_nodeImage
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (node : source.val.NodeId) :
    sourceNode result (result.nodeImage node) = node := by
  apply Fin.ext
  rfl

private theorem nodeImage_mem_nodesAt
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (region : source.val.RegionId)
    (node : source.val.NodeId)
    (member : node ∈ source.val.nodesAt region) :
    result.nodeImage node ∈
      result.checked.val.nodesAt (result.regionImage region) := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList at member ⊢
  apply List.mem_filter.mpr
  constructor
  · exact Data.Finite.mem_allFin _
  · have sourceRegion :=
      eq_of_beq (List.mem_filter.mp member).2
    have mappedRegion :=
      congrArg result.regionImage sourceRegion
    rw [result.node_generated]
    cases data : source.val.nodes node <;>
      simpa [data, IotaJoinResult.renameNode] using mappedRegion

private theorem sourceNode_mem_nodesAt
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (region : source.val.RegionId)
    (node : result.checked.val.NodeId)
    (member :
      node ∈ result.checked.val.nodesAt
        (result.regionImage region)) :
    sourceNode result node ∈ source.val.nodesAt region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList at member ⊢
  apply List.mem_filter.mpr
  constructor
  · exact Data.Finite.mem_allFin _
  · have targetRegion :=
      eq_of_beq (List.mem_filter.mp member).2
    have generated :=
      result.node_generated (sourceNode result node)
    rw [nodeImage_sourceNode] at generated
    rw [generated] at targetRegion
    have pulledRegion :=
      congrArg (sourceRegion result) targetRegion
    cases data : source.val.nodes (sourceNode result node) <;>
      simpa [data, IotaJoinResult.renameNode] using pulledRegion

private theorem denote_compileNodes_iff_singletons
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
        some items) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ node, node ∈ nodes →
        ∃ item,
          ConcreteElaboration.compileNodes? definitions diagram context
              [node] =
            some (.cons item .nil) ∧
          denoteItem pre definitionEnv env item := by
  induction nodes generalizing items with
  | nil =>
      simp only [ConcreteElaboration.compileNodes?] at compiled
      have itemsEmpty : items = .nil := Option.some.inj compiled.symm
      subst items
      simp
  | cons head tail induction =>
      obtain ⟨headItem, restItems, headCompiled, restCompiled,
          itemsEquation⟩ :=
        InsertionCompilation.NaturalityInternal.compileNodes_cons_components
          definitions diagram context head tail items compiled
      subst items
      rw [denoteItemSeq_cons, induction restItems restCompiled]
      constructor
      · rintro ⟨headDenotes, tailDenotes⟩ candidate member
        rcases List.mem_cons.mp member with equality | tailMember
        · subst candidate
          exact ⟨headItem, headCompiled, headDenotes⟩
        · exact tailDenotes candidate tailMember
      · intro each
        obtain ⟨actualHead, actualCompiled, headDenotes⟩ :=
          each head (by simp)
        have actualEquality : actualHead = headItem :=
          ItemSeq.cons.inj
            (Option.some.inj
              (actualCompiled.symm.trans headCompiled)) |>.1
        subst actualHead
        exact
          ⟨headDenotes, fun candidate tailMember =>
            each candidate (List.mem_cons_of_mem head tailMember)⟩

private theorem compileNodes_singleton_of_member
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
        some items)
    (node : diagram.NodeId)
    (member : node ∈ nodes) :
    ∃ item,
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
        some (.cons item .nil) := by
  induction nodes generalizing items with
  | nil => simp at member
  | cons head tail induction =>
      obtain ⟨headItem, restItems, headCompiled, restCompiled, _⟩ :=
        InsertionCompilation.NaturalityInternal.compileNodes_cons_components
          definitions diagram context head tail items compiled
      rcases List.mem_cons.mp member with equality | tailMember
      · subst node
        exact ⟨headItem, headCompiled⟩
      · exact induction restItems restCompiled tailMember

private theorem singleton_denotation
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (node : source.val.NodeId)
    (sourceItem : Item definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceContext [node] =
        some (.cons sourceItem .nil))
    (targetItem : Item definitions targetContext.sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          targetContext [result.nodeImage node] =
        some (.cons targetItem .nil)) :
    denoteItem pre definitionEnv targetEnv targetItem ↔
      denoteItem pre definitionEnv
        (Env.comp targetEnv (contextRenaming result related))
        sourceItem := by
  obtain ⟨expected, expectedCompiled, expectedEquation⟩ :=
    compile_singleton_natural result related targetNodup node
      sourceCompiled
  have targetEquation :
      (.cons targetItem .nil :
        ItemSeq definitions targetContext.sigs) =
        expected :=
    Option.some.inj (targetCompiled.symm.trans expectedCompiled)
  have sequenceEquation :
      (.cons targetItem .nil :
        ItemSeq definitions targetContext.sigs) =
        ((.cons sourceItem .nil :
          ItemSeq definitions sourceContext.sigs).renameWires
          (contextRenaming result related)) :=
    targetEquation.trans expectedEquation
  have sequence :
      denoteItemSeq pre definitionEnv targetEnv
          (.cons targetItem .nil) ↔
        denoteItemSeq pre definitionEnv
          (Env.comp targetEnv (contextRenaming result related))
          (.cons sourceItem .nil) := by
    rw [sequenceEquation, denoteItemSeq_renameWires]
  simpa using sequence

theorem compiled_nodes_under_pullback
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (region : source.val.RegionId)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          (source.val.nodesAt region) =
        some sourceItems)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          targetContext
          (result.checked.val.nodesAt (result.regionImage region)) =
        some targetItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv (contextRenaming result related))
        sourceItems := by
  rw [denote_compileNodes_iff_singletons definitions
      result.checked.val targetContext pre definitionEnv targetEnv
      _ _ targetCompiled,
    denote_compileNodes_iff_singletons definitions source.val sourceContext
      pre definitionEnv
      (Env.comp targetEnv (contextRenaming result related))
      _ _ sourceCompiled]
  constructor
  · intro targetDenotes node sourceMember
    obtain ⟨sourceItem, sourceSingletonCompiled⟩ :=
      compileNodes_singleton_of_member definitions source.val sourceContext
        (source.val.nodesAt region) sourceItems sourceCompiled node
        sourceMember
    obtain ⟨targetItem, targetSingletonCompiled, targetItemDenotes⟩ :=
      targetDenotes (result.nodeImage node)
        (nodeImage_mem_nodesAt result region node sourceMember)
    exact
      ⟨sourceItem, sourceSingletonCompiled,
        (singleton_denotation result related targetNodup pre definitionEnv
          targetEnv node sourceItem sourceSingletonCompiled targetItem
          targetSingletonCompiled).mp targetItemDenotes⟩
  · intro sourceDenotes targetNode targetMember
    let node := sourceNode result targetNode
    have sourceMember :=
      sourceNode_mem_nodesAt result region targetNode targetMember
    obtain ⟨sourceItem, sourceSingletonCompiled, sourceItemDenotes⟩ :=
      sourceDenotes node sourceMember
    obtain ⟨targetItem, targetSingletonCompiled⟩ :=
      compileNodes_singleton_of_member definitions result.checked.val
        targetContext
        (result.checked.val.nodesAt (result.regionImage region))
        targetItems targetCompiled targetNode targetMember
    have targetSingletonCompiled' :
        ConcreteElaboration.compileNodes? definitions result.checked.val
            targetContext [result.nodeImage node] =
          some (.cons targetItem .nil) := by
      rw [nodeImage_sourceNode]
      exact targetSingletonCompiled
    exact
      ⟨targetItem, targetSingletonCompiled,
        (singleton_denotation result related targetNodup pre definitionEnv
          targetEnv node sourceItem sourceSingletonCompiled targetItem
          targetSingletonCompiled').mpr sourceItemDenotes⟩

private theorem extendEnvironment_from
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (env : Env pre (context.extend region).sigs)
    (outerEnv : Env pre context.sigs)
    (agrees : ∀ {sig} (value : Var context.sigs sig),
      env sig
          (ConcreteElaboration.appendRightVar diagram
            (diagram.wiresAt region) value) =
        outerEnv sig value) :
    ConcreteElaboration.extendEnvironment diagram context region
        (ConcreteElaboration.valuesFromEnvironmentFor diagram context.ids
          (diagram.wiresAt region) env)
        outerEnv =
      env := by
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig value
  exact agrees value

private theorem contextRenaming_appendRight
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated result
        (sourceContext.extend region)
        (targetContext.extend (result.regionImage region)))
    (targetExtendedNodup :
      (targetContext.extend (result.regionImage region)).ids.Nodup)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    contextRenaming result extendedRelated
        (ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region) value) =
      ConcreteElaboration.appendRightVar result.checked.val
        (result.checked.val.wiresAt (result.regionImage region))
        (contextRenaming result related value) := by
  apply
    InsertionCompilation.NaturalityInternal.origin_injective
      result.checked.val
      (targetContext.extend (result.regionImage region)).ids
      targetExtendedNodup
  unfold ConcreteElaboration.WireContext.extend
  rw [contextRenaming_origin,
    ConcreteElaboration.origin_appendRightVar]
  change
    targetWire result
        (ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids value) =
      ConcreteElaboration.WireContext.origin result.checked.val
        (result.checked.val.wiresAt (result.regionImage region) ++
          targetContext.ids)
        (ConcreteElaboration.appendRightVar result.checked.val
          (result.checked.val.wiresAt (result.regionImage region))
          (contextRenaming result related value))
  rw [ConcreteElaboration.origin_appendRightVar,
    contextRenaming_origin]

private theorem contextSection_appendRight
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated result
        (sourceContext.extend region)
        (targetContext.extend (result.regionImage region)))
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    contextSection result extendedRelated
        (ConcreteElaboration.appendRightVar result.checked.val
          (result.checked.val.wiresAt (result.regionImage region)) value) =
      ConcreteElaboration.appendRightVar source.val
        (source.val.wiresAt region)
        (contextSection result related value) := by
  apply
    InsertionCompilation.NaturalityInternal.origin_injective source.val
      (sourceContext.extend region).ids sourceExtendedNodup
  unfold ConcreteElaboration.WireContext.extend
  rw [contextSection_origin,
    ConcreteElaboration.origin_appendRightVar]
  change
    sourceWire result
        (ConcreteElaboration.WireContext.origin result.checked.val
          targetContext.ids value) =
      ConcreteElaboration.WireContext.origin source.val
        (source.val.wiresAt region ++ sourceContext.ids)
        (ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region)
          (contextSection result related value))
  rw [ConcreteElaboration.origin_appendRightVar,
    contextSection_origin]

private theorem contextRenaming_section
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    contextRenaming result related
        (contextSection result related value) =
      value := by
  apply
    InsertionCompilation.NaturalityInternal.origin_injective
      result.checked.val targetContext.ids targetNodup
  rw [contextRenaming_origin, contextSection_origin,
    targetWire_sourceWire]

theorem target_extended_realizes_source
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated result
        (sourceContext.extend region)
        (targetContext.extend (result.regionImage region)))
    (targetExtendedNodup :
      (targetContext.extend (result.regionImage region)).ids.Nodup)
    (pre : PreModel)
    (sourceEnv : Env pre sourceContext.sigs)
    (targetEnv : Env pre targetContext.sigs)
    (outerRelated :
      sourceEnv =
        Env.comp targetEnv (contextRenaming result related))
    (targetValues : ConcreteElaboration.WireValues pre
      ((result.checked.val.wiresAt
        (result.regionImage region)).map fun wire =>
          (result.checked.val.wires wire).sig)) :
    let targetExtended :=
      ConcreteElaboration.extendEnvironment result.checked.val
        targetContext (result.regionImage region) targetValues targetEnv
    let sourceExtended :=
      Env.comp targetExtended
        (contextRenaming result extendedRelated)
    ConcreteElaboration.extendEnvironment source.val sourceContext region
        (ConcreteElaboration.valuesFromEnvironmentFor source.val
          sourceContext.ids (source.val.wiresAt region) sourceExtended)
        sourceEnv =
      sourceExtended := by
  simp only
  apply extendEnvironment_from
  intro sig value
  have sameVar :=
    contextRenaming_appendRight result related region extendedRelated
      targetExtendedNodup value
  change
    ConcreteElaboration.extendEnvironment result.checked.val
        targetContext (result.regionImage region) targetValues targetEnv sig
        (contextRenaming result extendedRelated
          (ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) value)) =
      sourceEnv sig value
  rw [sameVar,
    ConcreteElaboration.extendEnvironment_appendRightVar,
    outerRelated]
  rfl

theorem source_extended_realizes_target
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated result
        (sourceContext.extend region)
        (targetContext.extend (result.regionImage region)))
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (sourceEnv : Env pre sourceContext.sigs)
    (targetEnv : Env pre targetContext.sigs)
    (outerRelated :
      sourceEnv =
        Env.comp targetEnv (contextRenaming result related))
    (sourceValues : ConcreteElaboration.WireValues pre
      ((source.val.wiresAt region).map fun wire =>
        (source.val.wires wire).sig)) :
    let sourceExtended :=
      ConcreteElaboration.extendEnvironment source.val sourceContext region
        sourceValues sourceEnv
    let targetExtended :=
      Env.comp sourceExtended
        (contextSection result extendedRelated)
    ConcreteElaboration.extendEnvironment result.checked.val targetContext
        (result.regionImage region)
        (ConcreteElaboration.valuesFromEnvironmentFor result.checked.val
          targetContext.ids
          (result.checked.val.wiresAt (result.regionImage region))
          targetExtended)
        targetEnv =
      targetExtended := by
  simp only
  apply extendEnvironment_from
  intro sig value
  have sameVar :=
    contextSection_appendRight result related region extendedRelated
      sourceExtendedNodup value
  change
    ConcreteElaboration.extendEnvironment source.val sourceContext region
        sourceValues sourceEnv sig
        (contextSection result extendedRelated
          (ConcreteElaboration.appendRightVar result.checked.val
            (result.checked.val.wiresAt (result.regionImage region))
            value)) =
      targetEnv sig value
  rw [sameVar,
    ConcreteElaboration.extendEnvironment_appendRightVar,
    outerRelated]
  change
    targetEnv sig
        (contextRenaming result related
          (contextSection result related value)) =
      targetEnv sig value
  rw [contextRenaming_section result related targetNodup]

theorem pullback_one_point
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (targetEnv : Env pre targetContext.sigs) :
    let sourceEnv :=
      Env.comp targetEnv (contextRenaming result related)
    Env.comp
        (Env.comp sourceEnv (contextSection result related))
        (contextRenaming result related) =
      sourceEnv := by
  simp only
  funext sig value
  change
    targetEnv sig
        (contextRenaming result related
          (contextSection result related
            (contextRenaming result related value))) =
      targetEnv sig (contextRenaming result related value)
  rw [contextRenaming_section result related targetNodup]

theorem extended_one_point_without_local_inner
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated result
        (sourceContext.extend region)
        (targetContext.extend (result.regionImage region)))
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (targetExtendedNodup :
      (targetContext.extend (result.regionImage region)).ids.Nodup)
    (noLocalInner : inner ∉ source.val.wiresAt region)
    (pre : PreModel)
    (sourceEnv : Env pre sourceContext.sigs)
    (sourceOnePoint :
      Env.comp
          (Env.comp sourceEnv (contextSection result related))
          (contextRenaming result related) =
        sourceEnv)
    (sourceValues : ConcreteElaboration.WireValues pre
      ((source.val.wiresAt region).map fun wire =>
        (source.val.wires wire).sig)) :
    let sourceExtended :=
      ConcreteElaboration.extendEnvironment source.val sourceContext region
        sourceValues sourceEnv
    Env.comp
        (Env.comp sourceExtended
          (contextSection result extendedRelated))
        (contextRenaming result extendedRelated) =
      sourceExtended := by
  simp only
  funext sig value
  let wire :=
    ConcreteElaboration.WireContext.origin source.val
      (sourceContext.extend region).ids value
  have wireMember :
      wire ∈ source.val.wiresAt region ∨
        wire ∈ sourceContext.ids := by
    have member :=
      InsertionCompilation.NaturalityInternal.origin_member
        source.val (sourceContext.extend region).ids value
    simpa [ConcreteElaboration.WireContext.extend] using member
  rcases wireMember with localMember | outerMember
  · have survives : wire ≠ inner := by
      intro same
      apply noLocalInner
      simpa [same] using localMember
    have sectionOrigin :
        ConcreteElaboration.WireContext.origin source.val
            (sourceContext.extend region).ids
            (contextSection result extendedRelated
              (contextRenaming result extendedRelated value)) =
          wire := by
      rw [contextSection_origin, contextRenaming_origin,
        sourceWire_targetWire_of_survives result wire survives]
    have sameVariable :
        contextSection result extendedRelated
            (contextRenaming result extendedRelated value) =
          value :=
      InsertionCompilation.NaturalityInternal.origin_injective
        source.val (sourceContext.extend region).ids
        sourceExtendedNodup (by simpa [wire] using sectionOrigin)
    change
      ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceEnv sig
          (contextSection result extendedRelated
            (contextRenaming result extendedRelated value)) =
        ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceEnv sig value
    rw [sameVariable]
  · let outerVar :=
      InsertionCompilation.NaturalityInternal.varForMember
        source.val sourceContext.ids wire outerMember
    let signature : (source.val.wires wire).sig = sig :=
      ConcreteElaboration.WireContext.origin_signature source.val
        (sourceContext.extend region).ids value
    let outerVar' : Var sourceContext.sigs sig :=
      InsertionCompilation.NaturalityInternal.castVar
        signature outerVar
    have valueEquation :
        value =
          ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) outerVar' := by
      apply
        InsertionCompilation.NaturalityInternal.origin_injective
          source.val (sourceContext.extend region).ids
          sourceExtendedNodup
      unfold ConcreteElaboration.WireContext.extend
      rw [ConcreteElaboration.origin_appendRightVar]
      change
        wire =
          ConcreteElaboration.WireContext.origin source.val
            sourceContext.ids outerVar'
      calc
        wire =
            ConcreteElaboration.WireContext.origin source.val
              sourceContext.ids outerVar := by
          symm
          exact
            InsertionCompilation.NaturalityInternal.varForMember_origin
              source.val sourceContext.ids wire outerMember
        _ =
            ConcreteElaboration.WireContext.origin source.val
              sourceContext.ids outerVar' := by
          symm
          exact
            InsertionCompilation.NaturalityInternal.origin_castVar
              source.val sourceContext.ids signature outerVar
    rw [valueEquation]
    change
      ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceEnv sig
          (contextSection result extendedRelated
            (contextRenaming result extendedRelated
              (ConcreteElaboration.appendRightVar source.val
                (source.val.wiresAt region) outerVar'))) =
        ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceEnv sig
          (ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) outerVar')
    rw [contextRenaming_appendRight result related region
        extendedRelated targetExtendedNodup,
      contextSection_appendRight result related region
        extendedRelated sourceExtendedNodup,
      ConcreteElaboration.extendEnvironment_appendRightVar,
      ConcreteElaboration.extendEnvironment_appendRightVar]
    exact congrFun (congrFun sourceOnePoint sig) outerVar'

theorem regionImage_mem_childrenOf
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (region child : source.val.RegionId)
    (member : child ∈ source.val.childrenOf region) :
    result.regionImage child ∈
      result.checked.val.childrenOf (result.regionImage region) := by
  unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
    at member ⊢
  apply List.mem_filter.mpr
  constructor
  · exact Data.Finite.mem_allFin _
  · have childData := (List.mem_filter.mp member).2
    rw [result.region_generated]
    cases data : source.val.regions child <;>
      simp_all [IotaJoinResult.renameRegion]

theorem sourceRegion_mem_childrenOf
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (region : source.val.RegionId)
    (child : result.checked.val.RegionId)
    (member :
      child ∈
        result.checked.val.childrenOf (result.regionImage region)) :
    sourceRegion result child ∈ source.val.childrenOf region := by
  unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
    at member ⊢
  apply List.mem_filter.mpr
  constructor
  · exact Data.Finite.mem_allFin _
  · have childData := (List.mem_filter.mp member).2
    have generated :=
      result.region_generated (sourceRegion result child)
    rw [regionImage_sourceRegion] at generated
    rw [generated] at childData
    cases data : source.val.regions (sourceRegion result child) with
    | sheet =>
        simp [data, IotaJoinResult.renameRegion] at childData
    | cut parent =>
        simp [data, IotaJoinResult.renameRegion] at childData
        have pulled :=
          congrArg (sourceRegion result) childData
        simpa using pulled

theorem denote_compileChildren_iff_regions
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (children : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context children =
        some items) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ child, child ∈ children →
        ∃ body,
          recurse child context = some body ∧
            ¬ denoteRegion pre definitionEnv env body := by
  induction children generalizing items with
  | nil =>
      simp only [ConcreteElaboration.compileChildrenWith?] at compiled
      have itemsEmpty : items = .nil := Option.some.inj compiled.symm
      subst items
      simp
  | cons child tail induction =>
      obtain ⟨body, rest, bodyCompiled, restCompiled, itemsEquation⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions diagram recurse context child tail items compiled
      subst items
      rw [denoteItemSeq_cons, cut_denotes_negation,
        induction rest restCompiled]
      constructor
      · rintro ⟨bodyDenotes, tailDenotes⟩ candidate member
        rcases List.mem_cons.mp member with equality | tailMember
        · subst candidate
          exact ⟨body, bodyCompiled, bodyDenotes⟩
        · exact tailDenotes candidate tailMember
      · intro each
        obtain ⟨actualBody, actualCompiled, bodyDenotes⟩ :=
          each child (by simp)
        have actualEquality : actualBody = body :=
          Option.some.inj (actualCompiled.symm.trans bodyCompiled)
        subst actualBody
        exact
          ⟨bodyDenotes, fun candidate tailMember =>
            each candidate (List.mem_cons_of_mem child tailMember)⟩

theorem compileChild_of_member
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (children : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context children =
        some items)
    (child : diagram.RegionId)
    (member : child ∈ children) :
    ∃ body, recurse child context = some body := by
  induction children generalizing items with
  | nil => simp at member
  | cons head tail induction =>
      obtain ⟨body, rest, bodyCompiled, restCompiled, _⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions diagram recurse context head tail items compiled
      rcases List.mem_cons.mp member with equality | tailMember
      · subst child
        exact ⟨body, bodyCompiled⟩
      · exact induction rest restCompiled tailMember

private theorem compiled_children_equiv
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
        Option (Region definitions context.sigs))
    (targetRecurse :
      (region : result.checked.val.RegionId) →
      (context :
        ConcreteElaboration.WireContext result.checked.val) →
        Option (Region definitions context.sigs))
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext result.checked.val}
    (related : ContextsRelated result sourceContext targetContext)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (region : source.val.RegionId)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext (source.val.childrenOf region) =
        some sourceItems)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          result.checked.val targetRecurse targetContext
          (result.checked.val.childrenOf (result.regionImage region)) =
        some targetItems)
    (regions :
      ∀ child, child ∈ source.val.childrenOf region →
        ∀ sourceBody targetBody,
          sourceRecurse child sourceContext = some sourceBody →
          targetRecurse (result.regionImage child) targetContext =
            some targetBody →
          (denoteRegion pre definitionEnv targetEnv targetBody ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv
                (contextRenaming result related))
              sourceBody)) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv (contextRenaming result related))
        sourceItems := by
  rw [denote_compileChildren_iff_regions definitions
      result.checked.val targetRecurse targetContext pre definitionEnv
      targetEnv _ _ targetCompiled,
    denote_compileChildren_iff_regions definitions source.val
      sourceRecurse sourceContext pre definitionEnv
      (Env.comp targetEnv (contextRenaming result related))
      _ _ sourceCompiled]
  constructor
  · intro targetDenotes child sourceMember
    obtain ⟨sourceBody, sourceBodyCompiled⟩ :=
      compileChild_of_member definitions source.val sourceRecurse
        sourceContext (source.val.childrenOf region) sourceItems
        sourceCompiled child sourceMember
    obtain ⟨targetBody, targetBodyCompiled, targetNot⟩ :=
      targetDenotes (result.regionImage child)
        (regionImage_mem_childrenOf result region child sourceMember)
    exact
      ⟨sourceBody, sourceBodyCompiled,
        (not_congr
          (regions child sourceMember sourceBody targetBody
            sourceBodyCompiled targetBodyCompiled)).mp targetNot⟩
  · intro sourceDenotes targetChild targetMember
    let child := sourceRegion result targetChild
    have sourceMember :=
      sourceRegion_mem_childrenOf result region targetChild targetMember
    obtain ⟨sourceBody, sourceBodyCompiled, sourceNot⟩ :=
      sourceDenotes child sourceMember
    obtain ⟨targetBody, targetBodyCompiled⟩ :=
      compileChild_of_member definitions result.checked.val targetRecurse
        targetContext
        (result.checked.val.childrenOf (result.regionImage region))
        targetItems targetCompiled targetChild targetMember
    have targetBodyCompiled' :
        targetRecurse (result.regionImage child) targetContext =
          some targetBody := by
      rw [regionImage_sourceRegion]
      exact targetBodyCompiled
    exact
      ⟨targetBody, targetBodyCompiled,
        (not_congr
          (regions child sourceMember sourceBody targetBody
            sourceBodyCompiled targetBodyCompiled')).mpr sourceNot⟩

theorem compileRegion_equiv_below
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (comparable :
      source.val.Encloses
        (source.val.wires outer).scope
        (source.val.wires inner).scope)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∀ fuel
      {sourceContext : ConcreteElaboration.WireContext source.val}
      {targetContext :
        ConcreteElaboration.WireContext result.checked.val}
      (related : ContextsRelated result sourceContext targetContext)
      (region : source.val.RegionId)
      (sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceContext region)
      (targetAbove :
        ConcreteElaboration.ContextAbove result.checked.val targetContext
          (result.regionImage region))
      (targetCoverage :
        (targetContext.extend (result.regionImage region)).Covers
          (result.regionImage region))
      (safe :
        inner ∈ sourceContext.ids ∨
          ¬source.val.Encloses region (source.val.wires inner).scope)
      (sourceEnv : Env pre sourceContext.sigs)
      (targetEnv : Env pre targetContext.sigs)
      (outerRelated :
        sourceEnv =
          Env.comp targetEnv (contextRenaming result related))
      (sourceOnePoint :
        Env.comp
            (Env.comp sourceEnv (contextSection result related))
            (contextRenaming result related) =
          sourceEnv)
      {sourceBody : Region definitions sourceContext.sigs}
      {targetBody : Region definitions targetContext.sigs},
      ConcreteElaboration.compileRegion? definitions source.val fuel
          region sourceContext =
        some sourceBody →
      ConcreteElaboration.compileRegion? definitions result.checked.val fuel
          (result.regionImage region) targetContext =
        some targetBody →
      (denoteRegion pre definitionEnv targetEnv targetBody ↔
        denoteRegion pre definitionEnv sourceEnv sourceBody) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceContext targetContext related region sourceAbove
        targetAbove targetCoverage safe sourceEnv targetEnv
        outerRelated sourceOnePoint sourceBody targetBody sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel induction =>
      intro sourceContext targetContext related region sourceAbove
        targetAbove targetCoverage safe sourceEnv targetEnv
        outerRelated sourceOnePoint sourceBody targetBody sourceCompiled
        targetCompiled
      simp only [ConcreteElaboration.compileRegion?]
        at sourceCompiled targetCompiled
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
                (ConcreteElaboration.compileRegion? definitions source.val fuel)
                (sourceContext.extend region)
                (source.val.childrenOf region) with
          | none =>
              rw [sourceChildrenEquation] at sourceCompiled
              simp at sourceCompiled
          | some sourceChildren =>
              rw [sourceChildrenEquation] at sourceCompiled
              cases targetNodesEquation :
                  ConcreteElaboration.compileNodes? definitions
                    result.checked.val
                    (targetContext.extend (result.regionImage region))
                    (result.checked.val.nodesAt
                      (result.regionImage region)) with
              | none =>
                  rw [targetNodesEquation] at targetCompiled
                  simp at targetCompiled
              | some targetNodes =>
                  rw [targetNodesEquation] at targetCompiled
                  cases targetChildrenEquation :
                      ConcreteElaboration.compileChildrenWith? definitions
                        result.checked.val
                        (ConcreteElaboration.compileRegion? definitions
                          result.checked.val fuel)
                        (targetContext.extend (result.regionImage region))
                        (result.checked.val.childrenOf
                          (result.regionImage region)) with
                  | none =>
                      rw [targetChildrenEquation] at targetCompiled
                      simp at targetCompiled
                  | some targetChildren =>
                      rw [targetChildrenEquation] at targetCompiled
                      have sourceBodyEquality :
                          ConcreteElaboration.finishRegion source.val
                              sourceContext region
                              (.mk
                                (sourceNodes.append sourceChildren)) =
                            sourceBody :=
                        Option.some.inj sourceCompiled
                      have targetBodyEquality :
                          ConcreteElaboration.finishRegion result.checked.val
                              targetContext (result.regionImage region)
                              (.mk
                                (targetNodes.append targetChildren)) =
                            targetBody :=
                        Option.some.inj targetCompiled
                      subst sourceBody
                      subst targetBody
                      rw [ConcreteElaboration.denote_finishRegion,
                        ConcreteElaboration.denote_finishRegion]
                      let extendedRelated :=
                        extend_contexts_related result comparable related
                          region targetCoverage
                      have sourceExtendedNodup :=
                        ConcreteElaboration.extend_nodup definitions
                          source.val source.property sourceContext region
                          sourceAbove
                      have targetExtendedNodup :=
                        ConcreteElaboration.extend_nodup definitions
                          result.checked.val result.checked.property
                          targetContext (result.regionImage region)
                          targetAbove
                      have noLocalInner :
                          inner ∉ source.val.wiresAt region := by
                        intro localMember
                        rcases safe with innerVisible | outside
                        · have nodup := sourceExtendedNodup
                          rw [ConcreteElaboration.WireContext.extend,
                            List.nodup_append] at nodup
                          exact
                            nodup.2.2 inner localMember inner
                              innerVisible rfl
                        · apply outside
                          have scope :
                              (source.val.wires inner).scope = region :=
                            eq_of_beq
                              (List.mem_filter.mp localMember).2
                          rw [scope]
                          exact source.val.encloses_refl region
                      constructor
                      · rintro ⟨targetValues, targetCoreDenotes⟩
                        let targetExtended :=
                          ConcreteElaboration.extendEnvironment
                            result.checked.val targetContext
                            (result.regionImage region)
                            targetValues targetEnv
                        let sourceExtended :=
                          Env.comp targetExtended
                            (contextRenaming result extendedRelated)
                        let sourceValues :=
                          ConcreteElaboration.valuesFromEnvironmentFor
                            source.val sourceContext.ids
                            (source.val.wiresAt region) sourceExtended
                        have sourceRealizes :
                            ConcreteElaboration.extendEnvironment source.val
                                sourceContext region sourceValues sourceEnv =
                              sourceExtended :=
                          target_extended_realizes_source result related
                            region extendedRelated targetExtendedNodup pre
                            sourceEnv targetEnv outerRelated targetValues
                        refine ⟨sourceValues, ?_⟩
                        rw [sourceRealizes]
                        change
                          denoteItemSeq pre definitionEnv targetExtended
                            (targetNodes.append targetChildren)
                            at targetCoreDenotes
                        change
                          denoteItemSeq pre definitionEnv sourceExtended
                            (sourceNodes.append sourceChildren)
                        rw [denoteItemSeq_append] at targetCoreDenotes ⊢
                        have extendedOnePoint :=
                          pullback_one_point result extendedRelated
                            targetExtendedNodup pre targetExtended
                        constructor
                        · exact
                            (compiled_nodes_under_pullback result
                              extendedRelated targetExtendedNodup pre
                              definitionEnv targetExtended region sourceNodes
                              sourceNodesEquation targetNodes
                              targetNodesEquation).mp targetCoreDenotes.1
                        · apply
                            (compiled_children_equiv result
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                result.checked.val fuel)
                              extendedRelated pre definitionEnv
                              targetExtended region sourceChildren
                              sourceChildrenEquation targetChildren
                              targetChildrenEquation ?_).mp
                              targetCoreDenotes.2
                          intro child childMember sourceChildBody
                            targetChildBody sourceChildCompiled
                            targetChildCompiled
                          have sourceChildData :=
                            ConcreteElaboration.mem_childrenOf source.val
                              region child childMember
                          have targetChildData :
                              result.checked.val.regions
                                  (result.regionImage child) =
                                .cut (result.regionImage region) := by
                            rw [result.region_generated]
                            simp [sourceChildData,
                              IotaJoinResult.renameRegion]
                          have sourceChildAbove :=
                            ConcreteElaboration.extend_above_child definitions
                              source.val source.property sourceContext region
                              child sourceAbove sourceChildData
                          have targetChildAbove :=
                            ConcreteElaboration.extend_above_child definitions
                              result.checked.val result.checked.property
                              targetContext (result.regionImage region)
                              (result.regionImage child) targetAbove
                              targetChildData
                          have targetChildCoverage :=
                            ConcreteElaboration.WireContext.extend_covers_child
                              result.checked.val
                              (targetContext.extend
                                (result.regionImage region))
                              (result.regionImage region)
                              (result.regionImage child)
                              targetCoverage targetChildData
                          have childSafe :
                              inner ∈
                                  (sourceContext.extend region).ids ∨
                                ¬source.val.Encloses child
                                  (source.val.wires inner).scope := by
                            rcases safe with innerVisible | outside
                            · exact .inl
                                (List.mem_append_right _ innerVisible)
                            · exact .inr fun childInner =>
                                outside
                                  (checked_encloses_trans definitions
                                    source.val source.property
                                    (InsertionCompilation.NaturalityInternal.parent_encloses_child
                                      source.val child region sourceChildData)
                                    childInner)
                          exact
                            induction extendedRelated child sourceChildAbove
                              targetChildAbove targetChildCoverage
                              childSafe sourceExtended
                              targetExtended rfl extendedOnePoint
                              sourceChildCompiled targetChildCompiled
                      · rintro ⟨sourceValues, sourceCoreDenotes⟩
                        let sourceExtended :=
                          ConcreteElaboration.extendEnvironment source.val
                            sourceContext region sourceValues sourceEnv
                        let targetExtended :=
                          Env.comp sourceExtended
                            (contextSection result extendedRelated)
                        let targetValues :=
                          ConcreteElaboration.valuesFromEnvironmentFor
                            result.checked.val targetContext.ids
                            (result.checked.val.wiresAt
                              (result.regionImage region))
                            targetExtended
                        have targetRealizes :
                            ConcreteElaboration.extendEnvironment
                                result.checked.val targetContext
                                (result.regionImage region)
                                targetValues targetEnv =
                              targetExtended :=
                          source_extended_realizes_target result related
                            region extendedRelated sourceExtendedNodup
                            targetAbove.1 pre sourceEnv targetEnv
                            outerRelated sourceValues
                        refine ⟨targetValues, ?_⟩
                        rw [targetRealizes]
                        change
                          denoteItemSeq pre definitionEnv sourceExtended
                            (sourceNodes.append sourceChildren)
                            at sourceCoreDenotes
                        change
                          denoteItemSeq pre definitionEnv targetExtended
                            (targetNodes.append targetChildren)
                        rw [denoteItemSeq_append] at sourceCoreDenotes ⊢
                        have extendedOnePoint :=
                          extended_one_point_without_local_inner result
                            related region extendedRelated
                            sourceExtendedNodup targetExtendedNodup
                            noLocalInner pre sourceEnv sourceOnePoint
                            sourceValues
                        have extendedEnvRelated :
                            sourceExtended =
                              Env.comp targetExtended
                                (contextRenaming result extendedRelated) :=
                          extendedOnePoint.symm
                        constructor
                        · exact
                            (compiled_nodes_under_pullback result
                              extendedRelated targetExtendedNodup pre
                              definitionEnv targetExtended region sourceNodes
                              sourceNodesEquation targetNodes
                              targetNodesEquation).mpr
                              (by
                                rw [← extendedEnvRelated]
                                exact sourceCoreDenotes.1)
                        · apply
                            (compiled_children_equiv result
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                result.checked.val fuel)
                              extendedRelated pre definitionEnv
                              targetExtended region sourceChildren
                              sourceChildrenEquation targetChildren
                              targetChildrenEquation ?_).mpr
                              (by
                                rw [← extendedEnvRelated]
                                exact sourceCoreDenotes.2)
                          intro child childMember sourceChildBody
                            targetChildBody sourceChildCompiled
                            targetChildCompiled
                          have sourceChildData :=
                            ConcreteElaboration.mem_childrenOf source.val
                              region child childMember
                          have targetChildData :
                              result.checked.val.regions
                                  (result.regionImage child) =
                                .cut (result.regionImage region) := by
                            rw [result.region_generated]
                            simp [sourceChildData,
                              IotaJoinResult.renameRegion]
                          have sourceChildAbove :=
                            ConcreteElaboration.extend_above_child definitions
                              source.val source.property sourceContext region
                              child sourceAbove sourceChildData
                          have targetChildAbove :=
                            ConcreteElaboration.extend_above_child definitions
                              result.checked.val result.checked.property
                              targetContext (result.regionImage region)
                              (result.regionImage child) targetAbove
                              targetChildData
                          have targetChildCoverage :=
                            ConcreteElaboration.WireContext.extend_covers_child
                              result.checked.val
                              (targetContext.extend
                                (result.regionImage region))
                              (result.regionImage region)
                              (result.regionImage child)
                              targetCoverage targetChildData
                          have childSafe :
                              inner ∈
                                  (sourceContext.extend region).ids ∨
                                ¬source.val.Encloses child
                                  (source.val.wires inner).scope := by
                            rcases safe with innerVisible | outside
                            · exact .inl
                                (List.mem_append_right _ innerVisible)
                            · exact .inr fun childInner =>
                                outside
                                  (checked_encloses_trans definitions
                                    source.val source.property
                                    (InsertionCompilation.NaturalityInternal.parent_encloses_child
                                      source.val child region sourceChildData)
                                    childInner)
                          rw [← extendedEnvRelated]
                          exact
                            induction extendedRelated child sourceChildAbove
                              targetChildAbove targetChildCoverage
                              childSafe sourceExtended
                              targetExtended extendedEnvRelated
                              extendedOnePoint sourceChildCompiled
                              targetChildCompiled

theorem compileRegion_target_implies_source_at_inner
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner)
    (comparable :
      source.val.Encloses
        (source.val.wires outer).scope
        (source.val.wires inner).scope)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∀ fuel
      {sourceContext : ConcreteElaboration.WireContext source.val}
      {targetContext :
        ConcreteElaboration.WireContext result.checked.val}
      (related : ContextsRelated result sourceContext targetContext)
      (sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceContext
          (source.val.wires inner).scope)
      (targetAbove :
        ConcreteElaboration.ContextAbove result.checked.val targetContext
          (result.regionImage (source.val.wires inner).scope))
      (targetCoverage :
        (targetContext.extend
          (result.regionImage (source.val.wires inner).scope)).Covers
            (result.regionImage (source.val.wires inner).scope))
      (sourceEnv : Env pre sourceContext.sigs)
      (targetEnv : Env pre targetContext.sigs)
      (outerRelated :
        sourceEnv =
          Env.comp targetEnv (contextRenaming result related))
      {sourceBody : Region definitions sourceContext.sigs}
      {targetBody : Region definitions targetContext.sigs},
      ConcreteElaboration.compileRegion? definitions source.val fuel
          (source.val.wires inner).scope sourceContext =
        some sourceBody →
      ConcreteElaboration.compileRegion? definitions result.checked.val fuel
          (result.regionImage (source.val.wires inner).scope)
          targetContext =
        some targetBody →
      denoteRegion pre definitionEnv targetEnv targetBody →
        denoteRegion pre definitionEnv sourceEnv sourceBody := by
  intro fuel
  cases fuel with
  | zero =>
      intro sourceContext targetContext related sourceAbove targetAbove
        targetCoverage sourceEnv targetEnv outerRelated sourceBody targetBody
        sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ childFuel =>
      intro sourceContext targetContext related sourceAbove targetAbove
        targetCoverage sourceEnv targetEnv outerRelated sourceBody targetBody
        sourceCompiled targetCompiled targetDenotes
      simp only [ConcreteElaboration.compileRegion?]
        at sourceCompiled targetCompiled
      cases sourceNodesEquation :
          ConcreteElaboration.compileNodes? definitions source.val
            (sourceContext.extend (source.val.wires inner).scope)
            (source.val.nodesAt (source.val.wires inner).scope) with
      | none =>
          rw [sourceNodesEquation] at sourceCompiled
          simp at sourceCompiled
      | some sourceNodes =>
          rw [sourceNodesEquation] at sourceCompiled
          cases sourceChildrenEquation :
              ConcreteElaboration.compileChildrenWith? definitions source.val
                (ConcreteElaboration.compileRegion? definitions source.val
                  childFuel)
                (sourceContext.extend (source.val.wires inner).scope)
                (source.val.childrenOf
                  (source.val.wires inner).scope) with
          | none =>
              rw [sourceChildrenEquation] at sourceCompiled
              simp at sourceCompiled
          | some sourceChildren =>
              rw [sourceChildrenEquation] at sourceCompiled
              cases targetNodesEquation :
                  ConcreteElaboration.compileNodes? definitions
                    result.checked.val
                    (targetContext.extend
                      (result.regionImage
                        (source.val.wires inner).scope))
                    (result.checked.val.nodesAt
                      (result.regionImage
                        (source.val.wires inner).scope)) with
              | none =>
                  rw [targetNodesEquation] at targetCompiled
                  simp at targetCompiled
              | some targetNodes =>
                  rw [targetNodesEquation] at targetCompiled
                  cases targetChildrenEquation :
                      ConcreteElaboration.compileChildrenWith? definitions
                        result.checked.val
                        (ConcreteElaboration.compileRegion? definitions
                          result.checked.val childFuel)
                        (targetContext.extend
                          (result.regionImage
                            (source.val.wires inner).scope))
                        (result.checked.val.childrenOf
                          (result.regionImage
                            (source.val.wires inner).scope)) with
                  | none =>
                      rw [targetChildrenEquation] at targetCompiled
                      simp at targetCompiled
                  | some targetChildren =>
                      rw [targetChildrenEquation] at targetCompiled
                      have sourceBodyEquality :
                          ConcreteElaboration.finishRegion source.val
                              sourceContext
                              (source.val.wires inner).scope
                              (.mk
                                (sourceNodes.append sourceChildren)) =
                            sourceBody :=
                        Option.some.inj sourceCompiled
                      have targetBodyEquality :
                          ConcreteElaboration.finishRegion result.checked.val
                              targetContext
                              (result.regionImage
                                (source.val.wires inner).scope)
                              (.mk
                                (targetNodes.append targetChildren)) =
                            targetBody :=
                        Option.some.inj targetCompiled
                      subst sourceBody
                      subst targetBody
                      rw [ConcreteElaboration.denote_finishRegion]
                        at targetDenotes
                      rw [ConcreteElaboration.denote_finishRegion]
                      obtain ⟨targetValues, targetCoreDenotes⟩ :=
                        targetDenotes
                      let extendedRelated :=
                        extend_contexts_related result comparable related
                          (source.val.wires inner).scope targetCoverage
                      have sourceExtendedNodup :=
                        ConcreteElaboration.extend_nodup definitions
                          source.val source.property sourceContext
                          (source.val.wires inner).scope sourceAbove
                      have targetExtendedNodup :=
                        ConcreteElaboration.extend_nodup definitions
                          result.checked.val result.checked.property
                          targetContext
                          (result.regionImage
                            (source.val.wires inner).scope)
                          targetAbove
                      let targetExtended :=
                        ConcreteElaboration.extendEnvironment
                          result.checked.val targetContext
                          (result.regionImage
                            (source.val.wires inner).scope)
                          targetValues targetEnv
                      let sourceExtended :=
                        Env.comp targetExtended
                          (contextRenaming result extendedRelated)
                      let sourceValues :=
                        ConcreteElaboration.valuesFromEnvironmentFor
                          source.val sourceContext.ids
                          (source.val.wiresAt
                            (source.val.wires inner).scope)
                          sourceExtended
                      have sourceRealizes :
                          ConcreteElaboration.extendEnvironment source.val
                              sourceContext
                              (source.val.wires inner).scope
                              sourceValues sourceEnv =
                            sourceExtended :=
                        target_extended_realizes_source result related
                          (source.val.wires inner).scope extendedRelated
                          targetExtendedNodup pre sourceEnv targetEnv
                          outerRelated targetValues
                      refine ⟨sourceValues, ?_⟩
                      rw [sourceRealizes]
                      change
                        denoteItemSeq pre definitionEnv targetExtended
                          (targetNodes.append targetChildren)
                          at targetCoreDenotes
                      change
                        denoteItemSeq pre definitionEnv sourceExtended
                          (sourceNodes.append sourceChildren)
                      rw [denoteItemSeq_append] at targetCoreDenotes ⊢
                      have extendedOnePoint :=
                        pullback_one_point result extendedRelated
                          targetExtendedNodup pre targetExtended
                      have innerVisible :
                          inner ∈
                            (sourceContext.extend
                              (source.val.wires inner).scope).ids := by
                        apply List.mem_append_left
                        unfold ConcreteDiagram.wiresAt
                        apply List.mem_filter.mpr
                        exact
                          ⟨Data.Finite.mem_allFin _, by simp⟩
                      constructor
                      · exact
                          (compiled_nodes_under_pullback result
                            extendedRelated targetExtendedNodup pre
                            definitionEnv targetExtended
                            (source.val.wires inner).scope sourceNodes
                            sourceNodesEquation targetNodes
                            targetNodesEquation).mp targetCoreDenotes.1
                      · apply
                          (compiled_children_equiv result
                            (ConcreteElaboration.compileRegion? definitions
                              source.val childFuel)
                            (ConcreteElaboration.compileRegion? definitions
                              result.checked.val childFuel)
                            extendedRelated pre definitionEnv targetExtended
                            (source.val.wires inner).scope sourceChildren
                            sourceChildrenEquation targetChildren
                            targetChildrenEquation ?_).mp
                            targetCoreDenotes.2
                        intro child childMember sourceChildBody
                          targetChildBody sourceChildCompiled
                          targetChildCompiled
                        have sourceChildData :=
                          ConcreteElaboration.mem_childrenOf source.val
                            (source.val.wires inner).scope child childMember
                        have targetChildData :
                            result.checked.val.regions
                                (result.regionImage child) =
                              .cut
                                (result.regionImage
                                  (source.val.wires inner).scope) := by
                          rw [result.region_generated]
                          simp [sourceChildData,
                            IotaJoinResult.renameRegion]
                        have sourceChildAbove :=
                          ConcreteElaboration.extend_above_child definitions
                            source.val source.property sourceContext
                            (source.val.wires inner).scope child sourceAbove
                            sourceChildData
                        have targetChildAbove :=
                          ConcreteElaboration.extend_above_child definitions
                            result.checked.val result.checked.property
                            targetContext
                            (result.regionImage
                              (source.val.wires inner).scope)
                            (result.regionImage child) targetAbove
                            targetChildData
                        have targetChildCoverage :=
                          ConcreteElaboration.WireContext.extend_covers_child
                            result.checked.val
                            (targetContext.extend
                              (result.regionImage
                                (source.val.wires inner).scope))
                            (result.regionImage
                              (source.val.wires inner).scope)
                            (result.regionImage child)
                            targetCoverage targetChildData
                        exact
                          compileRegion_equiv_below result comparable pre
                            definitionEnv childFuel extendedRelated child
                            sourceChildAbove targetChildAbove
                            targetChildCoverage (.inl innerVisible)
                            sourceExtended
                            targetExtended rfl extendedOnePoint
                            sourceChildCompiled targetChildCompiled

end IotaJoinSemantics

end ConcreteWireQuantifier

end VisualProof
