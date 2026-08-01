import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationConstruction
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCommonCore

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

private theorem targetAppliedSite_exists
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    ∃ targetSite : AppliedSite result.checked result.targetWire,
      targetSite ∈ result.targetSites.sites ∧
        targetSite.node = result.targetNode site := by
  have generated :=
    result.generatedNode_targetSiteNode result.targetSites site
  unfold argumentSiteNodes at generated
  obtain ⟨targetSite, member, exact⟩ := List.mem_map.mp generated
  exact ⟨targetSite, member, exact⟩

/-- Construction-owned target application corresponding to one ordered
source application.  The selection comes from the exhaustive checked target
site receipt rather than from an assumed target-list position. -/
noncomputable def targetAppliedSite
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    AppliedSite result.checked result.targetWire :=
  Classical.choose (targetAppliedSite_exists result site)

theorem targetAppliedSite_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    targetAppliedSite result site ∈ result.targetSites.sites :=
  (Classical.choose_spec (targetAppliedSite_exists result site)).1

@[simp]
theorem targetAppliedSite_node
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    (targetAppliedSite result site).node = result.targetNode site :=
  (Classical.choose_spec (targetAppliedSite_exists result site)).2

@[simp]
theorem targetAppliedSite_region
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    (targetAppliedSite result site).region =
      result.regionImage (result.sites.sites.get site).region := by
  have exact := congrArg CNode.region
    (targetAppliedSite result site).node_data
  rw [targetAppliedSite_node, result.targetNode_data] at exact
  simpa using exact.symm

/-- The generated target site's checked atom arity is the construction's
exact target relation arity. -/
theorem targetAppliedSite_argumentSignatures
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    (targetAppliedSite result site).argumentSignatures =
      result.targetArguments := by
  have exact := (targetAppliedSite result site).node_data.symm.trans
    (by simpa [targetAppliedSite_node] using result.targetNode_data site)
  exact CNode.atom.inj exact |>.2

/-- An accepted arity shift allocates one replacement reference beyond the
complete ordered source argument tuple at every generated site. -/
theorem arityShift_spec_arguments_length
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (site : Fin result.sites.sites.length) :
    (result.spec.arguments site).length =
      (result.sites.sites.get site).arguments.length + 1 := by
  unfold arityShift checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  unfold checkedArgumentSites at accepted
  rw [sites.checked] at accepted
  simp only at accepted
  change replaceAppliedEnds source wire sites
    (arityShiftSpec source wire sourceArguments sites newArgument) _ =
      .ok result at accepted
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        cases accepted
        simp [arityShiftSpec, existingReferences]

/-- The target site's concrete argument attachments are precisely the
retained source attachments followed by this site's canonical fresh local
wire. -/
theorem targetAppliedSite_arguments
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (site : Fin result.sites.sites.length) :
    (targetAppliedSite result site).arguments =
      (result.sites.sites.get site).arguments.map result.contextWireMap ++
        [result.targetLocalWire
          (Fin.cast (arityShift_localCount_exact source wire sourceArguments
            sourceSignature result.sites newArgument result accepted).symm
            site)] := by
  let sourceSite := result.sites.sites.get site
  let targetSite := targetAppliedSite result site
  have sourceArgumentSignatures :
      sourceSite.argumentSignatures = sourceArguments :=
    appliedSite_arguments_eq_relationArguments sourceArguments
      sourceSignature sourceSite
  have targetArgumentSignatures :
      targetSite.argumentSignatures = result.targetArguments :=
    targetAppliedSite_argumentSignatures result site
  have targetArgumentsExact :=
    arityShift_targetArguments_exact source wire sourceArguments
      sourceSignature sites newArgument result accepted
  have targetLength :
      targetSite.arguments.length = sourceSite.arguments.length + 1 := by
    rw [targetSite.arguments_length, targetArgumentSignatures,
      targetArgumentsExact, List.length_append, List.length_singleton,
      sourceSite.arguments_length, sourceArgumentSignatures]
  have expectedLength :
      ((result.sites.sites.get site).arguments.map result.contextWireMap ++
        [result.targetLocalWire
          (Fin.cast (arityShift_localCount_exact source wire sourceArguments
            sourceSignature result.sites newArgument result accepted).symm
            site)]).length = sourceSite.arguments.length + 1 := by
    simp [sourceSite]
  apply List.ext_get
  · rw [targetLength, List.length_append, List.length_map,
      List.length_singleton]
  · intro index targetBound expectedBound
    by_cases existing : index < sourceSite.arguments.length
    · have existingRaw :
          index < (result.sites.sites.get site).arguments.length := by
        simpa [sourceSite] using existing
      have referenceBound : index < (result.spec.arguments site).length := by
        rw [arityShift_spec_arguments_length source wire
          sourceArguments sourceSignature sites newArgument result accepted]
        omega
      have targetArgumentBound : index < result.targetArguments.length := by
        rw [← targetArgumentSignatures,
          ← targetSite.arguments_length]
        exact targetBound
      have targetOwner := targetSite.argument_owner index targetBound
      rw [targetAppliedSite_node] at targetOwner
      have constructionOwner :=
        arityShift_targetNode_existing_owner source wire sourceArguments
          sourceSignature sites newArgument result accepted site index
          existingRaw referenceBound targetArgumentBound
      have wireExact := Option.some.inj
        (targetOwner.symm.trans constructionOwner)
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by simpa using existing)]
      simpa [sourceSite, targetSite] using wireExact
    · have last : index = sourceSite.arguments.length := by
        rw [expectedLength] at expectedBound
        omega
      subst index
      have referenceBound :
          (result.sites.sites.get site).arguments.length <
            (result.spec.arguments site).length := by
        rw [arityShift_spec_arguments_length source wire
          sourceArguments sourceSignature sites newArgument result accepted]
        omega
      have targetArgumentBound : sourceSite.arguments.length <
          result.targetArguments.length := by
        rw [← targetArgumentSignatures,
          ← targetSite.arguments_length]
        exact targetBound
      have targetOwner := targetSite.argument_owner _ targetBound
      rw [targetAppliedSite_node] at targetOwner
      have constructionOwner :=
        arityShift_targetNode_local_owner source wire sourceArguments
          sourceSignature sites newArgument result accepted site
          referenceBound targetArgumentBound
      have wireExact := Option.some.inj
        (targetOwner.symm.trans constructionOwner)
      simp only [List.get_eq_getElem]
      simpa [sourceSite, targetSite] using wireExact

private theorem eraseDups_length_le
    [BEq α] [LawfulBEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.succ_le_succ_iff]
      exact Nat.le_trans
        (eraseDups_length_le
          (tail.filter fun value => !value == head))
        (List.length_filter_le _ tail)
termination_by values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem nodup_of_eraseDups_length_eq
    [BEq α] [LawfulBEq α]
    (values : List α)
    (exact : values.eraseDups.length = values.length) :
    values.Nodup := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons] at exact
      simp only [List.length_cons, Nat.succ.injEq] at exact
      let retained := tail.filter fun value => !value == head
      have retainedLength : retained.length = tail.length := by
        apply Nat.le_antisymm
        · exact List.length_filter_le _ tail
        · rw [← exact]
          exact eraseDups_length_le retained
      have retainedEquality : retained = tail :=
        List.Sublist.eq_of_length List.filter_sublist retainedLength
      rw [List.nodup_cons]
      constructor
      · intro member
        have accepted : (!head == head) = true := by
          have : head ∈ retained := by
            rw [retainedEquality]
            exact member
          exact (List.mem_filter.mp this).2
        simp at accepted
      · apply nodup_of_eraseDups_length_eq tail
        simpa [retained, retainedEquality] using exact
termination_by values.length
decreasing_by simp_wf

private theorem component_sublist_flatMap
    (values : List α)
    (value : α)
    (member : value ∈ values)
    (function : α → List β) :
    (function value).Sublist (values.flatMap function) := by
  induction values with
  | nil => contradiction
  | cons head tail induction =>
      rw [List.mem_cons] at member
      cases member with
      | inl same =>
          subst head
          exact List.sublist_append_left _ _
      | inr member =>
          exact (induction member).trans
            (List.sublist_append_right _ _)

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

private theorem move_to_front
    (value : α) (pre suffix : List α) :
    (value :: pre ++ suffix).Perm
      (pre ++ value :: suffix) := by
  induction pre with
  | nil => simp
  | cons head tail induction =>
      exact
        (List.Perm.swap value head (tail ++ suffix)).symm.trans
          (List.Perm.cons head induction)

private theorem perm_of_nodup_same_membership [DecidableEq α]
    {left right : List α}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (same : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons head tail =>
          have : head ∈ ([] : List α) :=
            (same head).mpr (by simp)
          contradiction
  | cons head tail induction =>
      have headMember : head ∈ right :=
        (same head).mp (by simp)
      obtain ⟨pre, suffix, rightExact⟩ :=
        List.append_of_mem headMember
      subst right
      have headNotTail : head ∉ tail :=
        (List.nodup_cons.mp leftNodup).1
      have rightParts := List.nodup_append.mp rightNodup
      have headNotPre : head ∉ pre := by
        intro member
        exact rightParts.2.2 head member head (by simp) rfl
      have headNotSuffix : head ∉ suffix :=
        (List.nodup_cons.mp rightParts.2.1).1
      have tailNodup : tail.Nodup :=
        (List.nodup_cons.mp leftNodup).2
      have restNodup : (pre ++ suffix).Nodup := by
        apply List.Sublist.nodup _ rightNodup
        exact List.Sublist.append (List.Sublist.refl pre)
          ((List.Sublist.refl suffix).cons head)
      have restSame : ∀ value,
          value ∈ tail ↔ value ∈ pre ++ suffix := by
        intro value
        constructor
        · intro member
          have inRight : value ∈ pre ++ head :: suffix :=
            (same value).mp (by simp [member])
          rw [List.mem_append] at inRight ⊢
          rcases inRight with inPre | inHead
          · exact Or.inl inPre
          · simp only [List.mem_cons] at inHead
            rcases inHead with exact | inSuffix
            · subst value; contradiction
            · exact Or.inr inSuffix
        · intro member
          have inRight : value ∈ pre ++ head :: suffix := by
            rw [List.mem_append] at member ⊢
            rcases member with inPre | inSuffix
            · exact Or.inl inPre
            · exact Or.inr (by simp [inSuffix])
          have inLeft := (same value).mpr inRight
          simp only [List.mem_cons] at inLeft
          rcases inLeft with exact | inTail
          · subst value
            rw [List.mem_append] at member
            rcases member with inPre | inSuffix <;> contradiction
          · exact inTail
      have restPerm : tail.Perm (pre ++ suffix) :=
        induction tailNodup restNodup restSame
      exact
        (List.Perm.cons head restPerm).trans
          (move_to_front head pre suffix)

/-- Every checked wire's stored endpoint sequence is duplicate-free. -/
theorem checkedWire_endpoints_nodup
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    (source.val.wires wire).endpoints.Nodup := by
  have allNodup :
      (source.val.endpointOccurrences.map Prod.snd).Nodup := by
    apply nodup_of_eraseDups_length_eq
    have exact := source.property.no_duplicate_endpoints
    unfold ConcreteDiagram.NoDuplicateEndpoints at exact
    simpa using exact
  have component :
      ((source.val.wires wire).endpoints.map fun endpoint =>
          (wire, endpoint)).Sublist source.val.endpointOccurrences := by
    unfold ConcreteDiagram.endpointOccurrences
    exact component_sublist_flatMap source.val.wiresList wire
      (Data.Finite.mem_allFin wire)
      (fun candidate =>
        (source.val.wires candidate).endpoints.map fun endpoint =>
          (candidate, endpoint))
  have endpointComponent := component.map Prod.snd
  have simplified :
      ((source.val.wires wire).endpoints.map fun endpoint =>
          (wire, endpoint)).map Prod.snd =
        (source.val.wires wire).endpoints := by
    simp [List.map_map, Function.comp_def]
  rw [simplified] at endpointComponent
  exact endpointComponent.nodup allNodup

/-- Exhaustively checked applications have pairwise-distinct source nodes. -/
theorem appliedSiteNodes_nodup
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    (sites.sites.map AppliedSite.node).Nodup := by
  have endpointsNodup := checkedWire_endpoints_nodup source wire
  rw [← sites.exhaustive] at endpointsNodup
  have general : ∀ values : List (AppliedSite source wire),
      (values.map AppliedSite.endpoint).Nodup →
        (values.map AppliedSite.node).Nodup := by
    intro values
    induction values with
    | nil => simp
    | cons head tail induction =>
        simp only [List.map_cons, List.nodup_cons]
        rintro ⟨headEndpointFresh, tailNodup⟩
        constructor
        · intro headNodeMember
          obtain ⟨candidate, candidateMember, nodeExact⟩ :=
            List.mem_map.mp headNodeMember
          apply headEndpointFresh
          apply List.mem_map.mpr
          refine ⟨candidate, candidateMember, ?_⟩
          unfold AppliedSite.endpoint
          exact congrArg (fun node => CEndpoint.mk node .head) nodeExact
        · exact induction tailNodup
  exact general sites.sites endpointsNodup

/-- Exhaustive site indices whose source applications are local to `region`,
preserving the acted wire's endpoint order. -/
def aritySitesAt
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (region : source.val.RegionId) :
    List (Fin sites.sites.length) :=
  (Data.Finite.allFin sites.sites.length).filter fun site =>
    (sites.sites.get site).region == region

/-- Operation-local fresh wires whose concrete scope is `region`, in their
construction order. -/
def arityFreshAt
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    List (Fin result.spec.localCount) :=
  (Data.Finite.allFin result.spec.localCount).filter fun fresh =>
    retainedRegion source (result.spec.localScope fresh) ==
      retainedRegion source region

/-- The operation-local fresh-wire order at a region is exactly the
endpoint/site order used by `aritySitesAt`. -/
theorem arityShift_freshSitesAt_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    (arityFreshAt result region).map
        (Fin.cast (arityShift_localCount_exact source wire sourceArguments
          sourceSignature result.sites newArgument result accepted)) =
      aritySitesAt result.sites region := by
  simpa [aritySitesAt] using
    arityShift_freshSitesAt source wire sourceArguments sourceSignature
      newArgument result accepted region

/-- Canonical positional equivalence from endpoint/site order to the fresh
local-wire suffix at a region. -/
noncomputable def arityFreshSiteOrder
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    Data.Finite.FiniteEquiv
      (Fin (aritySitesAt result.sites region).length)
      (Fin (arityFreshAt result region).length) := by
  apply finEquivOfEq
  have exact := congrArg List.length
    (arityShift_freshSitesAt_exact source wire sourceArguments
      sourceSignature newArgument result accepted region)
  simpa using exact.symm

/-- The fresh local selected by `arityFreshSiteOrder` is exactly the local
wire allocated for the corresponding endpoint-ordered application site. -/
theorem arityFreshSiteOrder_spec
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (index : Fin (aritySitesAt result.sites region).length) :
    Fin.cast (arityShift_localCount_exact source wire sourceArguments
        sourceSignature result.sites newArgument result accepted)
        ((arityFreshAt result region).get
          (arityFreshSiteOrder source wire sourceArguments sourceSignature
            newArgument result accepted region index)) =
      (aritySitesAt result.sites region).get index := by
  let same := arityShift_freshSitesAt_exact source wire sourceArguments
    sourceSignature newArgument result accepted region
  have selected := get_of_list_eq same index
  simpa only [List.get_eq_getElem, List.getElem_map,
    arityFreshSiteOrder, finEquivOfEq] using selected

/-- Endpoint/site holes and fresh local binders have the same cardinality. -/
theorem aritySitesAt_length_fresh
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    (aritySitesAt result.sites region).length =
      (arityFreshAt result region).length := by
  have exact := congrArg List.length
    (arityShift_freshSitesAt_exact source wire sourceArguments
      sourceSignature newArgument result accepted region)
  simpa using exact.symm

/-- Source application nodes local to `region`, preserving concrete node
order rather than endpoint order. -/
def sourceSiteNodesAt
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (region : source.val.RegionId) :
    List source.val.NodeId :=
  (source.val.nodesAt region).filter fun node =>
    decide (node ∈ argumentSiteNodes sites)

theorem aritySiteNodesAt_nodup
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (region : source.val.RegionId) :
    ((aritySitesAt sites region).map fun site =>
      (sites.sites.get site).node).Nodup := by
  have allExact :
      (Data.Finite.allFin sites.sites.length).map (fun site =>
          (sites.sites.get site).node) =
        sites.sites.map AppliedSite.node := by
    calc
      _ = ((Data.Finite.allFin sites.sites.length).map
            sites.sites.get).map AppliedSite.node := by
          simpa [Function.comp_def] using
            (List.map_map sites.sites.get AppliedSite.node
              (Data.Finite.allFin sites.sites.length)).symm
      _ = _ := congrArg (List.map AppliedSite.node)
        (map_get_allFin sites.sites)
  have filteredSublist :
      (aritySitesAt sites region).Sublist
        (Data.Finite.allFin sites.sites.length) :=
    List.filter_sublist
  have mappedSublist := filteredSublist.map fun site =>
    (sites.sites.get site).node
  rw [allExact] at mappedSublist
  exact mappedSublist.nodup (appliedSiteNodes_nodup sites)

theorem sourceSiteNodesAt_nodup
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (region : source.val.RegionId) :
    (sourceSiteNodesAt sites region).Nodup := by
  unfold sourceSiteNodesAt ConcreteDiagram.nodesAt
  exact (Data.Finite.allFin_nodup source.val.nodeCount).filter _ |>.filter _

theorem aritySiteNodesAt_mem_iff
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (region : source.val.RegionId)
    (node : source.val.NodeId) :
    node ∈ (aritySitesAt sites region).map (fun site =>
        (sites.sites.get site).node) ↔
      node ∈ sourceSiteNodesAt sites region := by
  constructor
  · intro member
    obtain ⟨site, siteMember, nodeExact⟩ := List.mem_map.mp member
    unfold aritySitesAt at siteMember
    have siteRegion := eq_of_beq (List.mem_filter.mp siteMember).2
    unfold sourceSiteNodesAt
    apply List.mem_filter.mpr
    constructor
    · unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
      apply List.mem_filter.mpr
      constructor
      · exact Data.Finite.mem_allFin node
      · rw [← nodeExact, (sites.sites.get site).node_data]
        exact beq_iff_eq.mpr siteRegion
    · apply decide_eq_true
      unfold argumentSiteNodes
      apply List.mem_map.mpr
      exact ⟨sites.sites.get site, List.get_mem _ _, nodeExact⟩
  · intro member
    unfold sourceSiteNodesAt at member
    obtain ⟨nodeAt, siteNode⟩ := List.mem_filter.mp member
    have siteNode := of_decide_eq_true siteNode
    unfold argumentSiteNodes at siteNode
    obtain ⟨site, siteMember, nodeExact⟩ := List.mem_map.mp siteNode
    obtain ⟨index, siteExact⟩ := List.get_of_mem siteMember
    apply List.mem_map.mpr
    refine ⟨index, ?_, ?_⟩
    · unfold aritySitesAt
      apply List.mem_filter.mpr
      refine ⟨Data.Finite.mem_allFin index, ?_⟩
      apply beq_iff_eq.mpr
      rw [siteExact]
      rw [ConcreteDiagram.nodesAt, List.mem_filter] at nodeAt
      have nodeRegion := eq_of_beq nodeAt.2
      rw [← nodeExact, site.node_data] at nodeRegion
      exact nodeRegion
    · rw [siteExact]
      exact nodeExact

/-- Source-node order and endpoint/site order contain the same number of
application holes at every region. -/
theorem sourceSiteNodesAt_length
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (region : source.val.RegionId) :
    (sourceSiteNodesAt sites region).length =
      (aritySitesAt sites region).length := by
  have permutation := perm_of_nodup_same_membership
    (aritySiteNodesAt_nodup sites region)
    (sourceSiteNodesAt_nodup sites region)
    (fun node => aritySiteNodesAt_mem_iff sites region node)
  simpa using permutation.length_eq.symm

/-- Concrete source-node holes and fresh local binders have the same
cardinality. -/
theorem sourceSiteNodesAt_length_fresh
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    (sourceSiteNodesAt result.sites region).length =
      (arityFreshAt result region).length :=
  (sourceSiteNodesAt_length result.sites region).trans
    (aritySitesAt_length_fresh source wire sourceArguments sourceSignature
      newArgument result accepted region)

/-- Canonical finite equivalence from endpoint/site order to source-node
order for the application holes local to one region. -/
noncomputable def aritySiteNodeOrder
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (region : source.val.RegionId) :
    Data.Finite.FiniteEquiv
      (Fin (aritySitesAt sites region).length)
      (Fin (sourceSiteNodesAt sites region).length) := by
  exact (finEquivOfEq (by simp)).trans
    (Data.Finite.FiniteEquiv.restrictLists
        (Data.Finite.FiniteEquiv.refl source.val.NodeId)
        ((aritySitesAt sites region).map fun site =>
          (sites.sites.get site).node)
        (sourceSiteNodesAt sites region)
        (aritySiteNodesAt_nodup sites region)
        (sourceSiteNodesAt_nodup sites region)
        (fun node => (aritySiteNodesAt_mem_iff sites region node).symm))

/-- The source node selected by the canonical order equivalence is the node
of the corresponding endpoint-ordered site. -/
theorem aritySiteNodeOrder_spec
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (region : source.val.RegionId)
    (index : Fin (aritySitesAt sites region).length) :
    (sourceSiteNodesAt sites region).get
        (aritySiteNodeOrder sites region index) =
      (sites.sites.get ((aritySitesAt sites region).get index)).node := by
  simpa [aritySiteNodeOrder, finEquivOfEq] using
    Data.Finite.FiniteEquiv.restrictLists_spec
    (Data.Finite.FiniteEquiv.refl source.val.NodeId)
    ((aritySitesAt sites region).map fun site =>
      (sites.sites.get site).node)
    (sourceSiteNodesAt sites region)
    (aritySiteNodesAt_nodup sites region)
    (sourceSiteNodesAt_nodup sites region)
    (fun node => (aritySiteNodesAt_mem_iff sites region node).symm)
    (finEquivOfEq (by simp) index)

/-- Normalize the endpoint/site-to-source-node permutation to the fresh
binder cardinality expected by `CylindricalHoles`. -/
noncomputable def aritySourceIndex
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    Data.Finite.FiniteEquiv
      (Fin (arityFreshAt result region).length)
      (Fin (arityFreshAt result region).length) :=
  (finEquivOfEq
      (aritySitesAt_length_fresh source wire sourceArguments sourceSignature
        newArgument result accepted region).symm).trans
    ((aritySiteNodeOrder result.sites region).trans
      (finEquivOfEq
        (sourceSiteNodesAt_length_fresh source wire sourceArguments
          sourceSignature newArgument result accepted region)))

/-- Normalize the endpoint/site-to-fresh positional equivalence to the
fresh binder cardinality expected by `CylindricalHoles`. -/
noncomputable def arityFreshIndex
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    Data.Finite.FiniteEquiv
      (Fin (arityFreshAt result region).length)
      (Fin (arityFreshAt result region).length) :=
  (finEquivOfEq
      (aritySitesAt_length_fresh source wire sourceArguments sourceSignature
        newArgument result accepted region).symm).trans
    (arityFreshSiteOrder source wire sourceArguments sourceSignature
      newArgument result accepted region)

theorem aritySourceIndex_spec
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (index : Fin (arityFreshAt result region).length) :
    (sourceSiteNodesAt result.sites region).get
        (Fin.cast
          (sourceSiteNodesAt_length_fresh source wire sourceArguments
            sourceSignature newArgument result accepted region).symm
          (aritySourceIndex source wire sourceArguments sourceSignature
            newArgument result accepted region index)) =
      (result.sites.sites.get
        ((aritySitesAt result.sites region).get
          (Fin.cast
            (aritySitesAt_length_fresh source wire sourceArguments
              sourceSignature newArgument result accepted region).symm
            index))).node := by
  simpa [aritySourceIndex, finEquivOfEq] using
    aritySiteNodeOrder_spec result.sites region
      (Fin.cast
        (aritySitesAt_length_fresh source wire sourceArguments
          sourceSignature newArgument result accepted region).symm index)

theorem arityFreshIndex_spec
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (index : Fin (arityFreshAt result region).length) :
    Fin.cast (arityShift_localCount_exact source wire sourceArguments
        sourceSignature result.sites newArgument result accepted)
        ((arityFreshAt result region).get
          (arityFreshIndex source wire sourceArguments sourceSignature
            newArgument result accepted region index)) =
      (aritySitesAt result.sites region).get
        (Fin.cast
          (aritySitesAt_length_fresh source wire sourceArguments
            sourceSignature newArgument result accepted region).symm
          index) := by
  simpa [arityFreshIndex, finEquivOfEq] using
    arityFreshSiteOrder_spec source wire sourceArguments sourceSignature
      newArgument result accepted region
      (Fin.cast
        (aritySitesAt_length_fresh source wire sourceArguments
          sourceSignature newArgument result accepted region).symm index)

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
