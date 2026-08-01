import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationFactorization

namespace VisualProof
namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

/-- Every checked replacement atom head is owned by the checker-selected
replacement relation wire. -/
theorem ArgumentResult.targetNode_head_owner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.endpointOwner?
        ⟨result.targetNode site, .head⟩ = some result.targetWire := by
  let endpoint : CEndpoint (replacementCandidate result.plan).nodeCount :=
    ⟨replacementNode result.plan site, .head⟩
  have required :
      CPort.head ∈ (replacementCandidate result.plan).requiredPorts
        (replacementNode result.plan site) := by
    unfold replacementCandidate
    rw [assigned_requiredPorts]
    simp [ConcreteDiagram.requiredPorts,
      replacementSkeleton_replacementNode]
  have raw := assigned_endpointOwner_required
    (replacementSkeleton result.plan) (replacementOwner result.plan)
    (replacementNode result.plan site) .head required
  have candidateOwner :
      (replacementCandidate result.plan).endpointOwner? endpoint =
        some (replacementCandidateWire result.plan) := by
    simpa [replacementCandidate, endpoint, replacementOwner,
      replacementCandidateWire, replacementNode] using raw
  have transported := Internal.checkedEndpoint_owner_transport
    result.generated endpoint
  rw [candidateOwner] at transported
  rw [result.targetWire_exact]
  exact transported

/-- Every required argument port of a checked replacement atom is owned by
the checked image of its construction-selected replacement owner. -/
theorem ArgumentResult.targetNode_argument_owner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (site : Fin result.sites.sites.length)
    (index : Nat)
    (bound : index < result.targetArguments.length) :
    result.checked.val.endpointOwner?
        ⟨result.targetNode site, .arg index⟩ =
      some (Internal.checkedWire result.generated
        (replacementOwner result.plan
          ⟨replacementNode result.plan site, .arg index⟩)) := by
  change index < result.spec.targetArguments.length at bound
  let endpoint : CEndpoint (replacementCandidate result.plan).nodeCount :=
    ⟨replacementNode result.plan site, .arg index⟩
  have required :
      CPort.arg index ∈ (replacementCandidate result.plan).requiredPorts
        (replacementNode result.plan site) := by
    unfold replacementCandidate
    rw [assigned_requiredPorts]
    simp [ConcreteDiagram.requiredPorts,
      replacementSkeleton_replacementNode, bound]
  have raw := assigned_endpointOwner_required
    (replacementSkeleton result.plan) (replacementOwner result.plan)
    (replacementNode result.plan site) (.arg index) required
  have candidateOwner :
      (replacementCandidate result.plan).endpointOwner? endpoint =
        some (replacementOwner result.plan endpoint) := by
    simpa [replacementCandidate, endpoint] using raw
  have transported := Internal.checkedEndpoint_owner_transport
    result.generated endpoint
  rw [candidateOwner] at transported
  exact transported

namespace ArgumentsSemantics

/-- Concrete source/target outer contexts retained by the recursive frame
construction for an accepted arity shift. -/
noncomputable def LocalCylindricalFrame.concretePair
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    result.FrameContextPair (ArgumentResult.RetainedContext.empty result)
      frame.sourceScope.frame frame.targetScope.frame :=
  result.actedScopeFramePair
    (arityShift_scopeLocalization source wire sourceArguments
      sourceSignature sites newArgument result accepted)
    frame.sourceScope frame.targetScope

/-- The executable factorization's shared outer signature block is exactly
the concrete source site-outer context preserved by construction. -/
theorem LocalCylindricalFrame.siteOuter_eq_concrete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.context.siteOuter =
      (frame.concretePair sourceArguments sourceSignature sites newArgument
        result accepted).sourceSiteOuter.sigs := by
  let pair := frame.concretePair sourceArguments sourceSignature sites
    newArgument result accepted
  have suffixExact : frame.context.siteOuter = pair.siteOuter := by
    exact List.append_cancel_left
      (frame.context.sourceVisibleExact.symm.trans pair.sourceVisibleExact)
  exact suffixExact.trans pair.siteOuter_exact

private theorem map_allFin_cast
    {left right : Nat} (same : left = right) :
    (Data.Finite.allFin left).map (Fin.cast same) =
      Data.Finite.allFin right := by
  subst right
  simp

/-- Before the appended arity position, the replacement atom retains each
checked source attachment in its original order. -/
theorem arityShift_argumentReference_existing
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (site : Fin result.sites.sites.length)
    (index : Nat)
    (existing : index < (result.sites.sites.get site).arguments.length)
    (bound : index < (result.spec.arguments site).length) :
    (result.spec.arguments site)[index]'bound =
      .existing ((result.sites.sites.get site).arguments[index]'existing) := by
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
        change
          (existingReferences (localCount := sites.sites.length)
            (sites.sites.get site).arguments ++ [.local site])[index] = _
        rw [List.getElem_append_left (by
          simpa [existingReferences] using existing)]
        exact List.getElem_map _

/-- The appended arity position at each replacement atom references exactly
that source occurrence's canonical operation-local wire. -/
theorem arityShift_argumentReference_local
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (site : Fin result.sites.sites.length)
    (bound : (result.sites.sites.get site).arguments.length <
      (result.spec.arguments site).length) :
    (result.spec.arguments site)[
        (result.sites.sites.get site).arguments.length]'bound =
      ArgumentReference.local
        (Fin.cast (arityShift_localCount_exact source wire sourceArguments
          sourceSignature result.sites newArgument result accepted).symm
          site) := by
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

/-- Each retained argument port of an arity-shifted atom is owned by the
canonical context image of the corresponding source attachment. -/
theorem arityShift_targetNode_existing_owner
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (site : Fin result.sites.sites.length)
    (index : Nat)
    (existing : index < (result.sites.sites.get site).arguments.length)
    (referenceBound : index < (result.spec.arguments site).length)
    (targetBound : index < result.targetArguments.length) :
    result.checked.val.endpointOwner?
        ⟨result.targetNode site, .arg index⟩ =
      some (result.contextWireMap
        ((result.sites.sites.get site).arguments[index]'existing)) := by
  rw [result.targetNode_argument_owner site index targetBound]
  let sourceWire :=
    (result.sites.sites.get site).arguments[index]'existing
  have different : sourceWire ≠ wire := by
    exact (result.sites.sites.get site).argument_ne_head index existing
  have retained : sourceWire ∉ result.sourceRemovedWires := by
    rw [arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]
    simpa [sourceWire] using different
  rw [result.contextWireMap_retained sourceWire retained]
  unfold replacementOwner replacementNode
  simp only [Fin.addCases_right]
  rw [List.getElem?_eq_getElem referenceBound,
    arityShift_argumentReference_existing source wire sourceArguments
      sourceSignature sites newArgument result accepted site index existing
      referenceBound]
  simp only
  have retainedMember : sourceWire ∈
      Internal.retainedWires source result.sourceRemovedWires := by
    unfold Internal.retainedWires
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin sourceWire, decide_eq_true retained⟩
  rw [retainedReplacementWire?_some result.plan sourceWire retainedMember]
  rfl

/-- The appended argument port of an arity-shifted atom is owned by that
source occurrence's canonical fresh local wire. -/
theorem arityShift_targetNode_local_owner
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (site : Fin result.sites.sites.length)
    (referenceBound : (result.sites.sites.get site).arguments.length <
      (result.spec.arguments site).length)
    (targetBound : (result.sites.sites.get site).arguments.length <
      result.targetArguments.length) :
    result.checked.val.endpointOwner?
        ⟨result.targetNode site,
          .arg (result.sites.sites.get site).arguments.length⟩ =
      some (result.targetLocalWire
        (Fin.cast (arityShift_localCount_exact source wire sourceArguments
          sourceSignature result.sites newArgument result accepted).symm
          site)) := by
  rw [result.targetNode_argument_owner site _ targetBound]
  unfold replacementOwner replacementNode
  simp only [Fin.addCases_right]
  rw [List.getElem?_eq_getElem referenceBound,
    arityShift_argumentReference_local source wire sourceArguments
      sourceSignature sites newArgument result accepted site referenceBound]
  rfl

/-- Filtering one concrete id from a duplicate-free compiler context removes
the exact typed position selected by that id's variable, even when other
binders carry the same signature. -/
theorem filter_origin_signatures
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    (selected :
      Var (ids.map fun wire => (diagram.wires wire).sig) signature) :
    ((ids.filter fun wire =>
        decide (wire ≠
          ConcreteElaboration.WireContext.origin diagram ids selected)).map
      fun wire => (diagram.wires wire).sig) =
      LocalHeadRemoval.eraseSelected selected := by
  induction ids with
  | nil => exact nomatch selected
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      cases selected with
      | here =>
          have tailExact :
              tail.filter (fun wire => !decide (wire = head)) = tail := by
            apply List.filter_eq_self.mpr
            intro candidate member
            have different : candidate ≠ head := by
              intro same
              subst candidate
              exact nodup.1 member
            simp [different]
          simp [ConcreteElaboration.WireContext.origin,
            LocalHeadRemoval.eraseSelected, tailExact]
      | there selected =>
          have headDifferent :
              head ≠ ConcreteElaboration.WireContext.origin
                diagram tail selected := by
            intro same
            apply nodup.1
            subst head
            exact ConcreteElaboration.Internal.origin_member diagram selected
          simpa [ConcreteElaboration.WireContext.origin, headDifferent,
            LocalHeadRemoval.eraseSelected] using
              congrArg (List.cons (diagram.wires head).sig)
                (induction nodup.2 selected)

/-- Ordered concrete context identifiers after deleting one intrinsically
selected typed position.  This is the identifier-level owner of the reduced
signature list used by `LocalHeadRemoval`. -/
def eraseSelectedIds
    (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) →
      Var (ids.map fun wire => (diagram.wires wire).sig) signature →
        List diagram.WireId
  | [], selected => nomatch selected
  | _head :: tail, .here => tail
  | head :: tail, .there selected =>
      head :: eraseSelectedIds diagram tail selected

/-- Deleting a typed position from concrete identifiers computes exactly the
same reduced signature vector as `LocalHeadRemoval.eraseSelected`. -/
theorem eraseSelectedIds_signatures
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (selected :
      Var (ids.map fun wire => (diagram.wires wire).sig) signature) :
    (eraseSelectedIds diagram ids selected).map
        (fun wire => (diagram.wires wire).sig) =
      LocalHeadRemoval.eraseSelected selected := by
  induction ids with
  | nil => exact nomatch selected
  | cons head tail induction =>
      cases selected with
      | here => rfl
      | there selected =>
          exact congrArg (List.cons (diagram.wires head).sig)
            (induction selected)

/-- Place a variable from the intrinsically reduced signature block directly
in the concrete identifier list with the selected origin deleted. -/
def retainedSelectedVarInErasedIds
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (selected :
      Var (ids.map fun wire => (diagram.wires wire).sig) headSignature)
    (value : Var (LocalHeadRemoval.eraseSelected selected) signature) :
    Var
      ((eraseSelectedIds diagram ids selected).map
        fun wire => (diagram.wires wire).sig)
      signature :=
  (eraseSelectedIds_signatures diagram ids selected).symm ▸ value

private theorem castVar_cons_here_symm
    (same : left = right) :
    (congrArg (List.cons head) same).symm ▸
        (Var.here : Var (head :: right) head) =
      (Var.here : Var (head :: left) head) := by
  cases same
  rfl

private theorem castVar_cons_there_symm
    (same : left = right)
    (value : Var right signature) :
    (congrArg (List.cons head) same).symm ▸
        (Var.there value : Var (head :: right) signature) =
      (Var.there (same.symm ▸ value) :
        Var (head :: left) signature) := by
  cases same
  rfl

/-- Direct typed deletion preserves the concrete origin of every retained
variable. -/
theorem eraseSelectedIds_origin_retainSelected
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (selected :
      Var (ids.map fun wire => (diagram.wires wire).sig) headSignature)
    (value : Var (LocalHeadRemoval.eraseSelected selected) signature) :
    ConcreteElaboration.WireContext.origin diagram
        (eraseSelectedIds diagram ids selected)
        (retainedSelectedVarInErasedIds diagram ids selected value) =
      ConcreteElaboration.WireContext.origin diagram ids
        (LocalHeadRemoval.retainSelected selected value) := by
  induction ids with
  | nil => exact nomatch selected
  | cons head tail induction =>
      cases selected with
      | here =>
          have proofExact :
              eraseSelectedIds_signatures diagram (head :: tail)
                  (Var.here : Var
                    ((head :: tail).map fun wire =>
                      (diagram.wires wire).sig)
                    (diagram.wires head).sig) = rfl :=
            Subsingleton.elim _ _
          unfold retainedSelectedVarInErasedIds
          change
            ConcreteElaboration.WireContext.origin diagram tail
                ((eraseSelectedIds_signatures diagram (head :: tail)
                  (Var.here : Var
                    ((head :: tail).map fun wire =>
                      (diagram.wires wire).sig)
                    (diagram.wires head).sig)).symm ▸ value) =
              ConcreteElaboration.WireContext.origin diagram tail value
          rw [proofExact]
      | there selected =>
          have proofExact :
              eraseSelectedIds_signatures diagram (head :: tail)
                  (Var.there selected) =
                congrArg (List.cons (diagram.wires head).sig)
                  (eraseSelectedIds_signatures diagram tail selected) :=
            Subsingleton.elim _ _
          unfold retainedSelectedVarInErasedIds
          change
            ConcreteElaboration.WireContext.origin diagram
                (head :: eraseSelectedIds diagram tail selected)
                ((eraseSelectedIds_signatures diagram (head :: tail)
                  (Var.there selected)).symm ▸ value) =
              ConcreteElaboration.WireContext.origin diagram (head :: tail)
                (LocalHeadRemoval.retainSelected
                  (Var.there selected) value)
          rw [proofExact]
          cases value with
          | here =>
              simp only [LocalHeadRemoval.eraseSelected,
                LocalHeadRemoval.retainSelected, WireRenaming.lift]
              let same :=
                eraseSelectedIds_signatures diagram tail selected
              have castExact := castVar_cons_here_symm
                (head := (diagram.wires head).sig) same
              calc
                _ = ConcreteElaboration.WireContext.origin diagram
                      (head :: eraseSelectedIds diagram tail selected)
                      (Var.here : Var
                        ((diagram.wires head).sig ::
                          (eraseSelectedIds diagram tail selected).map
                            fun wire => (diagram.wires wire).sig)
                        (diagram.wires head).sig) :=
                    congrArg
                      (ConcreteElaboration.WireContext.origin diagram
                        (head :: eraseSelectedIds diagram tail selected))
                      castExact
                _ = _ := rfl
          | there value =>
              simp only [LocalHeadRemoval.eraseSelected,
                LocalHeadRemoval.retainSelected, WireRenaming.lift]
              let same :=
                eraseSelectedIds_signatures diagram tail selected
              have castExact := castVar_cons_there_symm
                (head := (diagram.wires head).sig) same value
              calc
                _ = ConcreteElaboration.WireContext.origin diagram
                      (head :: eraseSelectedIds diagram tail selected)
                      (Var.there (same.symm ▸ value)) :=
                    congrArg
                      (ConcreteElaboration.WireContext.origin diagram
                        (head :: eraseSelectedIds diagram tail selected))
                      castExact
                _ = ConcreteElaboration.WireContext.origin diagram
                      (eraseSelectedIds diagram tail selected)
                      (same.symm ▸ value) := rfl
                _ = ConcreteElaboration.WireContext.origin diagram tail
                      (LocalHeadRemoval.retainSelected selected value) := by
                    simpa [same, retainedSelectedVarInErasedIds] using
                      induction selected value
                _ = _ := rfl

/-- The concrete identifier deletion for a stored removal has exactly that
removal's reduced signature index. -/
theorem eraseSelectedIds_removal_signatures
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (removal : LocalHeadRemoval headSignature
      (ids.map fun wire => (diagram.wires wire).sig) reduced) :
    (eraseSelectedIds diagram ids removal.head).map
        (fun wire => (diagram.wires wire).sig) = reduced :=
  (eraseSelectedIds_signatures diagram ids removal.head).trans
    removal.reduced_eq_erase_head.symm

/-- The concrete reduced context owned by a stored removal preserves the
origin of every variable retained by that receipt. -/
theorem eraseSelectedIds_origin_retain
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (removal : LocalHeadRemoval headSignature
      (ids.map fun wire => (diagram.wires wire).sig) reduced)
    (value : Var reduced signature) :
    ConcreteElaboration.WireContext.origin diagram
        (eraseSelectedIds diagram ids removal.head)
        (retainedSelectedVarInErasedIds diagram ids removal.head
          (removal.reduced_eq_erase_head ▸ value)) =
      ConcreteElaboration.WireContext.origin diagram ids
        (removal.retain value) := by
  calc
    _ = ConcreteElaboration.WireContext.origin diagram ids
          (LocalHeadRemoval.retainSelected removal.head
            (removal.reduced_eq_erase_head ▸ value)) :=
        eraseSelectedIds_origin_retainSelected diagram ids removal.head _
    _ = _ := congrArg
      (ConcreteElaboration.WireContext.origin diagram ids)
      (removal.retainSelected_head value)

/-- In a duplicate-free compiler context, filtering the selected concrete
origin is exactly the intrinsic ordered identifier deletion. -/
theorem filter_origin_ids
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    (selected :
      Var (ids.map fun wire => (diagram.wires wire).sig) signature) :
    ids.filter (fun wire => decide (wire ≠
        ConcreteElaboration.WireContext.origin diagram ids selected)) =
      eraseSelectedIds diagram ids selected := by
  induction ids with
  | nil => exact nomatch selected
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      cases selected with
      | here =>
          have tailExact :
              tail.filter (fun wire => !decide (wire = head)) = tail := by
            apply List.filter_eq_self.mpr
            intro candidate member
            have different : candidate ≠ head := by
              intro same
              subst candidate
              exact nodup.1 member
            simp [different]
          simp [ConcreteElaboration.WireContext.origin, eraseSelectedIds,
            tailExact]
      | there selected =>
          have headDifferent :
              head ≠ ConcreteElaboration.WireContext.origin
                diagram tail selected := by
            intro same
            apply nodup.1
            subst head
            exact ConcreteElaboration.Internal.origin_member diagram selected
          simpa [ConcreteElaboration.WireContext.origin, eraseSelectedIds,
            headDifferent] using congrArg (List.cons head)
              (induction nodup.2 selected)

theorem ArgumentResult.targetWire_ne_targetLocalWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (fresh : Fin result.spec.localCount) :
    result.targetWire ≠ result.targetLocalWire fresh := by
  rw [result.targetWire_exact]
  unfold ArgumentResult.targetLocalWire replacementCandidateWire
  intro same
  have values := congrArg Fin.val same
  simp [Internal.checkedWire, replacementCandidateLocalWire,
    replacementLocalWire, replacementHeadWire] at values

theorem ArgumentResult.targetWire_ne_retainedWireImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.targetWire ≠ result.retainedWireImage sourceWire retained := by
  rw [result.targetWire_exact]
  unfold ArgumentResult.retainedWireImage replacementCandidateWire
  intro same
  have values := congrArg Fin.val same
  simp [Internal.checkedWire, replacementHeadWire] at values
  omega

/-- Exact ordered target-local wire layout for an accepted arity shift.
Retained source locals remain first, followed by the replacement relation
head and the operation-local fresh wires. -/
theorem arityShift_wiresAt_shape
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    result.checked.val.wiresAt (result.regionImage region) =
      ((source.val.wiresAt region).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap ++
        ((Data.Finite.allFin 1).filter fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source region).map (fun _head =>
              result.targetWire) ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region).map result.targetLocalWire := by
  rw [result.wiresAt_decomposition]
  have baseSources := batchRemovalCandidate_wiresAt_sources
    result.plan.removal region
  rw [← retainedRegion_eq_noRegionRemovalEquiv] at baseSources
  change
    ((replacementBase result.plan).wiresAt
        (retainedRegion source region)).map
          (Internal.sourceRetainedWire source result.sourceRemovedWires) =
      (source.val.wiresAt region).filter
        (fun sourceWire =>
          decide (sourceWire ∉ result.sourceRemovedWires)) at baseSources
  have retainedExact :
      ((replacementBase result.plan).wiresAt
          (retainedRegion source region)).map (fun retained =>
            Internal.checkedWire result.generated
              (Fin.castAdd (1 + result.spec.localCount) retained)) =
        ((source.val.wiresAt region).filter
          (fun sourceWire => decide
            (sourceWire ∉ result.sourceRemovedWires))).map
          result.contextWireMap := by
    calc
      _ = ((replacementBase result.plan).wiresAt
            (retainedRegion source region)).map (fun retained =>
              result.contextWireMap
                (Internal.sourceRetainedWire source
                  result.sourceRemovedWires retained)) := by
          apply List.map_congr_left
          intro retained _member
          have sourceRetained :
              Internal.sourceRetainedWire source result.sourceRemovedWires
                  retained ∉ result.sourceRemovedWires := by
            have member := List.get_mem
              (Internal.retainedWires source result.sourceRemovedWires)
              retained
            exact of_decide_eq_true (List.mem_filter.mp member).2
          rw [result.contextWireMap_retained _ sourceRetained]
          unfold ArgumentResult.retainedWireImage
          apply congrArg (Internal.checkedWire result.generated)
          exact congrArg (Fin.castAdd (1 + result.spec.localCount))
            (Internal.retainedWireIndex_sourceRetainedWire source
              result.sourceRemovedWires retained).symm
      _ = (((replacementBase result.plan).wiresAt
            (retainedRegion source region)).map
              (Internal.sourceRetainedWire source
                result.sourceRemovedWires)).map result.contextWireMap := by
          rw [List.map_map]
          apply List.map_congr_left
          intro retained _member
          rfl
      _ = ((source.val.wiresAt region).filter
            (fun sourceWire => decide
              (sourceWire ∉ result.sourceRemovedWires))).map
            result.contextWireMap := by rw [baseSources]
  rw [retainedExact,
    arityShift_sourceRemovedWires_exact source wire newArgument result
      accepted]

/-- Below the acted relation head, every source-local binder is retained in
order and the construction appends exactly the fresh binders scoped at that
region. -/
theorem arityShift_localSignatures_below
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope) :
    (result.checked.val.wiresAt (result.regionImage region)).map
        (fun targetWire => (result.checked.val.wires targetWire).sig) =
      (source.val.wiresAt region).map
          (fun sourceWire => (source.val.wires sourceWire).sig) ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region).map (fun _ => newArgument) := by
  have retainedAll :
      (source.val.wiresAt region).filter
          (fun sourceWire => decide (sourceWire ∉ [wire])) =
        source.val.wiresAt region := by
    apply List.filter_eq_self.mpr
    intro sourceWire member
    apply decide_eq_true
    simp only [List.mem_singleton]
    intro same
    subst sourceWire
    rw [ConcreteDiagram.wiresAt, List.mem_filter] at member
    have scopeExact := eq_of_beq member.2
    exact notHead scopeExact.symm
  have headEmpty :
      (Data.Finite.allFin 1).filter (fun _head =>
        retainedRegion source (source.val.wires wire).scope ==
          retainedRegion source region) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro head _member acceptedHead
    have retainedExact := eq_of_beq acceptedHead
    have scopeExact : (source.val.wires wire).scope = region := by
      apply (ConcreteWireQuantifier.Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact retainedExact
    exact notHead scopeExact.symm
  rw [arityShift_localSignatures_shape source wire sourceArguments
    sourceSignature result.sites newArgument result accepted region,
    retainedAll, headEmpty]
  simp

/-- Canonical binder certificate for every region below the acted head. -/
def arityShift_regionBounds_below
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope) :
    BoundCylindrification newArgument
      ((source.val.wiresAt region).map fun sourceWire =>
        (source.val.wires sourceWire).sig)
      ((result.checked.val.wiresAt (result.regionImage region)).map
        fun targetWire => (result.checked.val.wires targetWire).sig)
      ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
        retainedRegion source (result.spec.localScope fresh) ==
          retainedRegion source region).length := by
  rw [arityShift_localSignatures_below source wire sourceArguments
    sourceSignature newArgument result accepted region notHead]
  rw [List.map_const']
  exact BoundCylindrification.appendFresh newArgument _ _

/-- Fresh arity wires scoped at one region have exactly the same order as
the corresponding checked source occurrences at that region. -/
theorem arityShift_freshSitesAt
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
        retainedRegion source (result.spec.localScope fresh) ==
          retainedRegion source region).map
        (Fin.cast (arityShift_localCount_exact source wire sourceArguments
          sourceSignature result.sites newArgument result accepted)) =
      (Data.Finite.allFin result.sites.sites.length).filter fun site =>
        (result.sites.sites.get site).region == region := by
  let countExact := arityShift_localCount_exact source wire sourceArguments
    sourceSignature result.sites newArgument result accepted
  have predicates :
      (Data.Finite.allFin result.spec.localCount).filter (fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region) =
        (Data.Finite.allFin result.spec.localCount).filter
          ((fun site : Fin result.sites.sites.length =>
            (result.sites.sites.get site).region == region) ∘
            Fin.cast countExact) := by
    apply List.filter_congr
    intro fresh _member
    simp only [Function.comp_apply]
    apply decide_eq_decide.mpr
    let site := Fin.cast countExact fresh
    have scopeExact := arityShift_localScope_exact source wire sourceArguments
      sourceSignature result.sites newArgument result accepted site
    have freshExact : Fin.cast countExact.symm site = fresh := by
      apply Fin.ext
      rfl
    rw [freshExact] at scopeExact
    rw [scopeExact]
    constructor
    · intro retainedExact
      apply
        (ConcreteWireQuantifier.Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact retainedExact
    · intro same
      rw [same]
  rw [predicates, ← List.filter_map, map_allFin_cast countExact]

/-- The normalized source binder block is exactly the source scope's ordered
local signatures with the selected relation head removed. -/
theorem LocalCylindricalFrame.sourceReduced_shape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    ((source.val.wiresAt (source.val.wires wire).scope).filter
        (fun sourceWire => decide (sourceWire ∉ [wire]))).map
        (fun sourceWire => (source.val.wires sourceWire).sig) =
      frame.sourceReduced := by
  have localNodup :
      (source.val.wiresAt (source.val.wires wire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup source.val.wireCount).filter _
  have filtered := filter_origin_signatures source.val
    (source.val.wiresAt (source.val.wires wire).scope) localNodup
    frame.sourceHead
  rw [frame.sourceHead_origin] at filtered
  calc
    _ = LocalHeadRemoval.eraseSelected frame.sourceHead := by
      simpa using filtered
    _ = LocalHeadRemoval.eraseSelected frame.sourceRemoval.head := by
      rw [frame.sourceRemoval_head]
    _ = frame.sourceReduced :=
      frame.sourceRemoval.reduced_eq_erase_head.symm

/-- Deleting the replacement head from the target's exact local-wire layout
leaves the retained source locals followed by precisely the local fresh
arity wires. -/
theorem arityShift_targetLocals_withoutHead
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result) :
    (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope).filter
          (fun targetWire => decide (targetWire ≠ result.targetWire)) =
      ((source.val.wiresAt (source.val.wires wire).scope).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
              result.targetLocalWire := by
  have layout := arityShift_wiresAt_shape source wire newArgument result
    accepted (source.val.wires wire).scope
  rw [← result.targetWire_scope_regionImage] at layout
  have headLocal :
      ((Data.Finite.allFin 1).filter fun _head =>
        retainedRegion source (source.val.wires wire).scope ==
          retainedRegion source (source.val.wires wire).scope).map
          (fun _head => result.targetWire) = [result.targetWire] := by
    simp [Data.Finite.allFin_eq_finRange, List.finRange]
  rw [headLocal] at layout
  rw [layout, List.filter_append, List.filter_append]
  have retainedAll :
      (((source.val.wiresAt (source.val.wires wire).scope).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap).filter
            (fun targetWire => decide (targetWire ≠ result.targetWire)) =
        ((source.val.wiresAt (source.val.wires wire).scope).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          result.contextWireMap := by
    apply List.filter_eq_self.mpr
    intro targetWire targetMember
    obtain ⟨sourceWire, sourceMember, targetExact⟩ :=
      List.mem_map.mp targetMember
    subst targetWire
    apply decide_eq_true
    have sourceRetained : sourceWire ∉ result.sourceRemovedWires := by
      rw [arityShift_sourceRemovedWires_exact source wire newArgument result
        accepted]
      exact of_decide_eq_true (List.mem_filter.mp sourceMember).2
    rw [result.contextWireMap_retained sourceWire sourceRetained]
    exact
      (VisualProof.ConcreteWirePrimitive.ArgumentsSemantics.ArgumentResult.targetWire_ne_retainedWireImage
        result sourceWire sourceRetained).symm
  have freshAll :
      (((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
          result.targetLocalWire).filter
            (fun targetWire => decide (targetWire ≠ result.targetWire)) =
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
          result.targetLocalWire := by
    apply List.filter_eq_self.mpr
    intro targetWire targetMember
    obtain ⟨fresh, _freshMember, targetExact⟩ :=
      List.mem_map.mp targetMember
    subst targetWire
    exact decide_eq_true
      (VisualProof.ConcreteWirePrimitive.ArgumentsSemantics.ArgumentResult.targetWire_ne_targetLocalWire
        result fresh).symm
  rw [retainedAll, freshAll]
  simp

/-- The normalized target's concrete reduced local identifiers are exactly
the canonical images of the normalized source locals followed by the fresh
arity suffix owned by construction. -/
theorem LocalCylindricalFrame.targetReducedIds_shape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    eraseSelectedIds result.checked.val
        (result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope)
        frame.targetRemoval.head =
      (eraseSelectedIds source.val
          (source.val.wiresAt (source.val.wires wire).scope)
          frame.sourceRemoval.head).map result.contextWireMap ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
              result.targetLocalWire := by
  have sourceNodup :
      (source.val.wiresAt (source.val.wires wire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup source.val.wireCount).filter _
  have targetNodup :
      (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup result.checked.val.wireCount).filter _
  rw [← filter_origin_ids result.checked.val _ targetNodup
    frame.targetRemoval.head]
  rw [← filter_origin_ids source.val _ sourceNodup
    frame.sourceRemoval.head]
  rw [frame.targetRemoval_head, frame.targetHead_origin,
    frame.sourceRemoval_head, frame.sourceHead_origin]
  simpa using arityShift_targetLocals_withoutHead source wire newArgument
    result accepted

/-- Concrete source context containing precisely the retained local binders
after the selected relation head is deleted. -/
def LocalCylindricalFrame.sourceReducedContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    ConcreteElaboration.WireContext source.val :=
  ⟨eraseSelectedIds source.val
    (source.val.wiresAt (source.val.wires wire).scope)
    frame.sourceRemoval.head⟩

/-- Canonical target image of the retained source-local context, before the
fresh arity suffix is appended. -/
def LocalCylindricalFrame.mappedSourceReducedContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    ConcreteElaboration.WireContext result.checked.val :=
  ⟨frame.sourceReducedContext.ids.map result.contextWireMap⟩

/-- Concrete target context obtained by deleting the replacement relation
head while retaining the construction-owned fresh arity suffix. -/
def LocalCylindricalFrame.targetReducedContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    ConcreteElaboration.WireContext result.checked.val :=
  ⟨eraseSelectedIds result.checked.val
    (result.checked.val.wiresAt
      (result.checked.val.wires result.targetWire).scope)
    frame.targetRemoval.head⟩

/-- The concrete source-reduced context has exactly the intrinsic signature
block stored by the source head-removal receipt. -/
theorem LocalCylindricalFrame.sourceReducedContext_sigs
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.sourceReducedContext.sigs = frame.sourceReduced :=
  eraseSelectedIds_removal_signatures source.val
    (source.val.wiresAt (source.val.wires wire).scope)
    frame.sourceRemoval

/-- The concrete target-reduced context has exactly the intrinsic signature
block stored by the target head-removal receipt. -/
theorem LocalCylindricalFrame.targetReducedContext_sigs
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.targetReducedContext.sigs = frame.targetReduced :=
  eraseSelectedIds_removal_signatures result.checked.val
    (result.checked.val.wiresAt
      (result.checked.val.wires result.targetWire).scope)
    frame.targetRemoval

/-- Concrete target-reduced identifiers are the mapped retained source block
followed by the exact construction-owned fresh block at the acted scope. -/
theorem LocalCylindricalFrame.targetReducedContext_ids
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.targetReducedContext.ids =
      frame.mappedSourceReducedContext.ids ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
              result.targetLocalWire := by
  exact frame.targetReducedIds_shape sourceArguments newArgument result
    accepted

/-- The reduced source-local context and its mapped target image form a
genuine retained context; the acted relation head is the only removed source
wire in an arity shift. -/
def LocalCylindricalFrame.reducedRetainedContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    {sourceArguments : List Sig}
    (frame : LocalCylindricalFrame result sourceArguments) :
    result.RetainedContext frame.sourceReducedContext
      frame.mappedSourceReducedContext := by
  refine
    { ids_exact := rfl
      source_retained := ?_ }
  intro sourceWire member
  have sourceNodup :
      (source.val.wiresAt (source.val.wires wire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup source.val.wireCount).filter _
  have erasedExact : frame.sourceReducedContext.ids =
      (source.val.wiresAt (source.val.wires wire).scope).filter
        (fun candidate => decide (candidate ≠ wire)) := by
    unfold sourceReducedContext
    rw [← filter_origin_ids source.val _ sourceNodup
      frame.sourceRemoval.head]
    rw [frame.sourceRemoval_head, frame.sourceHead_origin]
  rw [arityShift_sourceRemovedWires_exact source wire newArgument result
    accepted]
  simp only [List.mem_singleton]
  rw [erasedExact, List.mem_filter] at member
  exact of_decide_eq_true member.2

/-- After both relation heads are normalized into explicit outer slots, the
target binder block is the source block followed by the exact local fresh
suffix. -/
theorem LocalCylindricalFrame.targetReduced_shape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.targetReduced =
      frame.sourceReduced ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).map
              (fun _ => newArgument) := by
  let freshAtScope :=
    (Data.Finite.allFin result.spec.localCount).filter fun fresh =>
      retainedRegion source (result.spec.localScope fresh) ==
        retainedRegion source (source.val.wires wire).scope
  have targetNodup :
      (result.checked.val.wiresAt
        (result.checked.val.wires result.targetWire).scope).Nodup := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    exact (Data.Finite.allFin_nodup result.checked.val.wireCount).filter _
  have filtered := filter_origin_signatures result.checked.val
    (result.checked.val.wiresAt
      (result.checked.val.wires result.targetWire).scope) targetNodup
    frame.targetHead
  rw [frame.targetHead_origin] at filtered
  have layout := arityShift_targetLocals_withoutHead source wire newArgument
    result accepted
  calc
    frame.targetReduced =
        LocalHeadRemoval.eraseSelected frame.targetRemoval.head :=
      frame.targetRemoval.reduced_eq_erase_head
    _ = LocalHeadRemoval.eraseSelected frame.targetHead := by
      rw [frame.targetRemoval_head]
    _ = ((result.checked.val.wiresAt
          (result.checked.val.wires result.targetWire).scope).filter
            (fun targetWire => decide
              (targetWire ≠ result.targetWire))).map
          (fun targetWire => (result.checked.val.wires targetWire).sig) :=
      filtered.symm
    _ = ((((source.val.wiresAt
            (source.val.wires wire).scope).filter
              (fun sourceWire => decide (sourceWire ∉ [wire]))).map
            result.contextWireMap) ++
          freshAtScope.map result.targetLocalWire).map
            (fun targetWire => (result.checked.val.wires targetWire).sig) := by
      rw [layout]
    _ = frame.sourceReduced ++ freshAtScope.map (fun _ => newArgument) := by
      rw [List.map_append, List.map_map, List.map_map]
      congr 1
      · calc
          _ = ((source.val.wiresAt
                (source.val.wires wire).scope).filter
                  (fun sourceWire => decide (sourceWire ∉ [wire]))).map
                (fun sourceWire => (source.val.wires sourceWire).sig) := by
            apply List.map_congr_left
            intro sourceWire sourceMember
            have sourceRetained :
                sourceWire ∉ result.sourceRemovedWires := by
              rw [arityShift_sourceRemovedWires_exact source wire newArgument
                result accepted]
              exact of_decide_eq_true (List.mem_filter.mp sourceMember).2
            exact result.contextWireMap_signature sourceWire sourceRetained
          _ = frame.sourceReduced := frame.sourceReduced_shape
      · apply List.map_congr_left
        intro fresh _freshMember
        simp only [Function.comp_apply]
        rw [result.targetLocalWire_signature]
        exact arityShift_localSignature_exact source wire sourceArguments
          sourceSignature result.sites newArgument result accepted fresh

/-- The target root binder block is the source block followed by a canonical
constant-signature suffix, stated in the representation consumed directly by
`BoundCylindrification.appendFresh`. -/
theorem LocalCylindricalFrame.rootReducedExact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    frame.targetReduced =
      frame.sourceReduced ++ List.replicate
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
        retainedRegion source (result.spec.localScope fresh) ==
          retainedRegion source (source.val.wires wire).scope).length
        newArgument := by
  rw [frame.targetReduced_shape sourceArguments sourceSignature newArgument
    result accepted]
  rw [List.map_const']

/-- Canonical root binder certificate: retain the normalized source block and
append exactly the fresh wires whose scope is the acted scope. -/
def LocalCylindricalFrame.rootBounds
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments) :
    BoundCylindrification newArgument frame.sourceReduced frame.targetReduced
      ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
        retainedRegion source (result.spec.localScope fresh) ==
          retainedRegion source (source.val.wires wire).scope).length :=
  (frame.rootReducedExact sourceArguments sourceSignature newArgument result
    accepted).symm ▸
    BoundCylindrification.appendFresh newArgument frame.sourceReduced _

/-- The construction-owned root bound certificate retains every source
local at the same ordinal before its canonical fresh suffix. -/
theorem LocalCylindricalFrame.rootBounds_embedLocal
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (frame : LocalCylindricalFrame result sourceArguments)
    (value : Var frame.sourceReduced signature) :
    (frame.rootReducedExact sourceArguments sourceSignature newArgument result
        accepted) ▸
        ((frame.rootBounds sourceArguments sourceSignature newArgument result
          accepted).embedLocal value) =
      Var.appendLeft value
        (List.replicate
          ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source (source.val.wires wire).scope).length
          newArgument) := by
  unfold LocalCylindricalFrame.rootBounds
  rw [BoundCylindrification.embedLocal_transport]
  exact BoundCylindrification.appendFresh_embedLocal _ _ _ value

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
