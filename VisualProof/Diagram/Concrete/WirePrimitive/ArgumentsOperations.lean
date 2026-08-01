import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCommonCore
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsConstructionNaturality

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

/-- A successful replacement retains the exact number of operation-local
wires requested by its construction specification. -/
theorem replaceAppliedEnds_localCount_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result) :
    result.spec.localCount = spec.localCount := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

/-- A successful replacement retains the operation-local signature function
requested by its construction specification. -/
theorem replaceAppliedEnds_localSignature_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result)
    (fresh : Fin result.spec.localCount) :
    result.spec.localSignature fresh =
      spec.localSignature
        (Fin.cast
          (replaceAppliedEnds_localCount_exact source wire sites spec
            sourceRemovedExhausted result accepted) fresh) := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

/-- A successful replacement retains the operation-local scope function
requested by its construction specification. -/
theorem replaceAppliedEnds_localScope_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result)
    (fresh : Fin result.spec.localCount) :
    result.spec.localScope fresh =
      spec.localScope
        (Fin.cast
          (replaceAppliedEnds_localCount_exact source wire sites spec
            sourceRemovedExhausted result accepted) fresh) := by
  unfold replaceAppliedEnds at accepted
  split at accepted <;> try contradiction
  next removal _ =>
    simp only at accepted
    split at accepted <;> try contradiction
    next checked _ =>
      split at accepted <;> try contradiction
      next targetSites _ =>
        have resultExact := Except.ok.inj accepted
        subst result
        rfl

/-- A successful replacement retains its caller-proved scope-locality facts;
the checked construction cannot substitute a different removal or local-wire
specification. -/
theorem replaceAppliedEnds_scopeLocalization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites)
    (sourceRemovedExhausted :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
          endpoint.node ∈ argumentSiteNodes sites)
    (removedEnclosed :
      ∀ sourceWire, sourceWire ∈ wire :: spec.removedWires →
        source.val.Encloses (source.val.wires wire).scope
          (source.val.wires sourceWire).scope)
    (localEnclosed :
      ∀ fresh : Fin spec.localCount,
        source.val.Encloses (source.val.wires wire).scope
          (spec.localScope fresh))
    (result : ArgumentResult source wire)
    (accepted :
      replaceAppliedEnds source wire sites spec sourceRemovedExhausted =
        .ok result) :
    result.ScopeLocalization := by
  unfold replaceAppliedEnds at accepted
  split at accepted
  · contradiction
  · simp only at accepted
    split at accepted
    · contradiction
    · split at accepted
      · contradiction
      · cases accepted
        exact
          { removed_enclosed := by
              intro sourceWire removed
              exact removedEnclosed sourceWire removed
            local_enclosed := localEnclosed }

private theorem arityShiftSpec_argument_existing
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (site : Fin sites.sites.length)
    (index : Nat)
    (existing : index < (sites.sites.get site).arguments.length)
    (bound : index <
      ((arityShiftSpec source wire relationArguments sites newArgument).arguments
        site).length) :
    ((arityShiftSpec source wire relationArguments sites newArgument).arguments
        site)[index]'bound =
        ArgumentReference.existing
          ((sites.sites.get site).arguments[index]'existing) := by
  change
    (existingReferences (localCount := sites.sites.length)
      (sites.sites.get site).arguments ++ [.local site])[index] = _
  rw [List.getElem_append_left (by
    simpa [existingReferences] using existing)]
  exact List.getElem_map _

private theorem arityShiftSpec_argument_local
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (site : Fin sites.sites.length)
    (bound : (sites.sites.get site).arguments.length <
      ((arityShiftSpec source wire relationArguments sites newArgument).arguments
        site).length) :
    ((arityShiftSpec source wire relationArguments sites newArgument).arguments
      site)[(sites.sites.get site).arguments.length]'bound =
        ArgumentReference.local site := by
  simp [arityShiftSpec, existingReferences]

private theorem arityShiftSpec_target_existing
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (index : Nat) (bound : index < relationArguments.length)
    (targetBound : index <
      (ReplacementSpec.targetArguments
        (arityShiftSpec source wire relationArguments sites newArgument)).length) :
    getElem
        (ReplacementSpec.targetArguments
          (arityShiftSpec source wire relationArguments sites newArgument))
        index targetBound =
      getElem relationArguments index bound := by
  exact List.getElem_append_left bound

private theorem arityShiftSpec_target_local
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (bound : relationArguments.length <
      (ReplacementSpec.targetArguments
        (arityShiftSpec source wire relationArguments sites newArgument)).length) :
    getElem
        (ReplacementSpec.targetArguments
          (arityShiftSpec source wire relationArguments sites newArgument))
        relationArguments.length bound = newArgument := by
  simp [arityShiftSpec]

private theorem arityShiftSpec_valid
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sourceSignature : (source.val.wires wire).sig = .rel relationArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig) :
    ReplacementValid
      (arityShiftSpec source wire relationArguments sites newArgument) := by
  let spec := arityShiftSpec source wire relationArguments sites newArgument
  have siteArgumentsExact : ∀ site : Fin sites.sites.length,
      (sites.sites.get site).argumentSignatures = relationArguments := by
    intro site
    exact appliedSite_arguments_eq_relationArguments relationArguments
      sourceSignature (sites.sites.get site)
  refine
    { argumentsLength := ?_
      retained := ?_
      signature := ?_
      visible := ?_
      removedExhausted := ?_ }
  · intro site
    simp only [spec, arityShiftSpec, existingReferences,
      List.length_append, List.length_map, List.length_cons, List.length_nil]
    rw [(sites.sites.get site).arguments_length, siteArgumentsExact site]
  · intro site index bound
    by_cases existing : index < (sites.sites.get site).arguments.length
    · have valueExact :
          (spec.arguments site)[index]'bound =
            .existing ((sites.sites.get site).arguments[index]'existing) := by
        exact arityShiftSpec_argument_existing source wire
          relationArguments sites newArgument site index existing bound
      rw [valueExact]
      simp only [arityShiftSpec, List.mem_singleton]
      change (sites.sites.get site).arguments[index] ≠ wire
      exact (sites.sites.get site).argument_ne_head index existing
    · have last : index = (sites.sites.get site).arguments.length := by
        have lengthExact :
            ((arityShiftSpec source wire relationArguments sites
              newArgument).arguments site).length =
              (sites.sites.get site).arguments.length + 1 := by
          simp [arityShiftSpec, existingReferences]
        omega
      subst index
      rw [arityShiftSpec_argument_local source wire relationArguments sites
        newArgument site bound]
      trivial
  · intro site index bound
    by_cases existing : index < (sites.sites.get site).arguments.length
    · have targetBound : index < relationArguments.length := by
        rw [← siteArgumentsExact site,
          ← (sites.sites.get site).arguments_length]
        exact existing
      have valueExact :
          (spec.arguments site)[index]'bound =
            .existing ((sites.sites.get site).arguments[index]'existing) := by
        exact arityShiftSpec_argument_existing source wire
          relationArguments sites newArgument site index existing bound
      rw [valueExact]
      rw [arityShiftSpec_target_existing source wire relationArguments sites
        newArgument index targetBound]
      have argumentSignature :=
        (sites.sites.get site).argument_signature index existing
      have same := siteArgumentsExact site
      subst relationArguments
      exact argumentSignature
    · have last : index = (sites.sites.get site).arguments.length := by
        have lengthExact :
            ((arityShiftSpec source wire relationArguments sites
              newArgument).arguments site).length =
              (sites.sites.get site).arguments.length + 1 := by
          simp [arityShiftSpec, existingReferences]
        omega
      subst index
      have lengthExact :
          (sites.sites.get site).arguments.length =
            relationArguments.length := by
        rw [(sites.sites.get site).arguments_length,
          siteArgumentsExact site]
      rw [arityShiftSpec_argument_local source wire relationArguments sites
        newArgument site bound]
      simpa only [lengthExact] using
        (arityShiftSpec_target_local source wire relationArguments sites
          newArgument _).symm
  · intro site index bound
    by_cases existing : index < (sites.sites.get site).arguments.length
    · have valueExact :
          (spec.arguments site)[index]'bound =
            .existing ((sites.sites.get site).arguments[index]'existing) := by
        exact arityShiftSpec_argument_existing source wire
          relationArguments sites newArgument site index existing bound
      rw [valueExact]
      exact (sites.sites.get site).argument_visible index existing
    · have last : index = (sites.sites.get site).arguments.length := by
        have lengthExact :
            ((arityShiftSpec source wire relationArguments sites
              newArgument).arguments site).length =
              (sites.sites.get site).arguments.length + 1 := by
          simp [arityShiftSpec, existingReferences]
        omega
      subst index
      rw [arityShiftSpec_argument_local source wire relationArguments sites
        newArgument site bound]
      change source.val.Encloses
        (sites.sites.get site).region (sites.sites.get site).region
      exact ConcreteDiagram.encloses_refl _ _
  · intro sourceWire removed endpoint member
    have same : sourceWire = wire := by simpa [spec, arityShiftSpec] using removed
    subst sourceWire
    exact allAppliedSites_removed_exhausted sites endpoint member

private theorem head_only_removed_exhausted
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (sourceWire : source.val.WireId)
    (removed : sourceWire ∈ [wire])
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires sourceWire).endpoints) :
    endpoint.node ∈ argumentSiteNodes sites := by
  have same : sourceWire = wire := by simpa using removed
  subst sourceWire
  exact allAppliedSites_removed_exhausted sites endpoint incident

/-- Add one locally scoped fresh argument at every applied end. -/
def arityShift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  let sites ← checkedArgumentSites source wire
  let spec := arityShiftSpec source wire relationArguments sites newArgument
  replaceAppliedEnds source wire sites spec (by
    intro sourceWire removed endpoint incident
    exact head_only_removed_exhausted sites sourceWire
      (by simpa [spec, arityShiftSpec] using removed) endpoint incident)

/--
Arity shift cannot fail once the acted relation signature and exhaustive
applied-site receipt have been checked.
-/
theorem arityShift_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel relationArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig) :
    ∃ result, arityShift source wire newArgument = .ok result := by
  unfold arityShift checkedRelationArguments relationArguments?
  rw [sourceSignature]
  simp only
  unfold checkedArgumentSites
  rw [sites.checked]
  simp only
  exact replaceAppliedEnds_complete source wire sites
    (arityShiftSpec source wire relationArguments sites newArgument)
    (arityShiftSpec_valid source wire relationArguments sourceSignature sites
      newArgument)

/--
Arity shift also constructs an exhaustive applied-site receipt for its fresh
relation head.  Later semantic layers consume this construction-owned result
instead of treating target-site rediscovery as a possible failure.
-/
theorem arityShift_complete_with_targetSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel relationArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig) :
    ∃ result,
      arityShift source wire newArgument = .ok result ∧
        ∃ targetSites,
          checkAllAppliedSites result.checked result.targetWire =
            some targetSites := by
  unfold arityShift checkedRelationArguments relationArguments?
  rw [sourceSignature]
  simp only
  unfold checkedArgumentSites
  rw [sites.checked]
  simp only
  exact replaceAppliedEnds_complete_with_targetSites source wire sites
    (arityShiftSpec source wire relationArguments sites newArgument)
    (arityShiftSpec_valid source wire relationArguments sourceSignature sites
      newArgument)

/-- Arity shift deletes exactly the acted source head and no ambient wire. -/
theorem arityShift_sourceRemovedWires_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result) :
    result.sourceRemovedWires = [wire] := by
  unfold arityShift at accepted
  cases relationAccepted : checkedRelationArguments source wire with
  | error error =>
      rw [relationAccepted] at accepted
      contradiction
  | ok relationArguments =>
      rw [relationAccepted] at accepted
      cases sitesAccepted : checkedArgumentSites source wire with
      | error error =>
          rw [sitesAccepted] at accepted
          contradiction
      | ok sites =>
          rw [sitesAccepted] at accepted
          have exact :=
            replaceAppliedEnds_sourceRemovedWires_exact source wire sites
              (arityShiftSpec source wire relationArguments sites newArgument)
              _ result accepted
          simpa [arityShiftSpec] using exact

/-- The total arity-shift construction appends exactly the requested
signature to the source relation's ordered argument vector. -/
theorem arityShift_targetArguments_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel relationArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result) :
    result.targetArguments = relationArguments ++ [newArgument] := by
  unfold arityShift checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  unfold checkedArgumentSites at accepted
  rw [sites.checked] at accepted
  simp only at accepted
  have exact :=
    replaceAppliedEnds_targetArguments_exact source wire sites
      (arityShiftSpec source wire relationArguments sites newArgument)
      _ result accepted
  simpa [arityShiftSpec] using exact

/-- Arity shift allocates exactly one operation-local argument wire for every
exhaustively checked source occurrence. -/
theorem arityShift_localCount_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel relationArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result) :
    result.spec.localCount = result.sites.sites.length := by
  unfold arityShift checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  unfold checkedArgumentSites at accepted
  rw [sites.checked] at accepted
  simp only at accepted
  have sitesExact := replaceAppliedEnds_sites_exact source wire sites
    (arityShiftSpec source wire relationArguments sites newArgument) _
    result accepted
  calc
    result.spec.localCount =
        (arityShiftSpec source wire relationArguments sites newArgument).localCount :=
      replaceAppliedEnds_localCount_exact source wire sites
        (arityShiftSpec source wire relationArguments sites newArgument) _
        result accepted
    _ = sites.sites.length := rfl
    _ = result.sites.sites.length := by rw [sitesExact]

/-- Every operation-local wire created by arity shift carries the inserted
signature. -/
theorem arityShift_localSignature_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel relationArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (fresh : Fin result.spec.localCount) :
    result.spec.localSignature fresh = newArgument := by
  unfold arityShift checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  unfold checkedArgumentSites at accepted
  rw [sites.checked] at accepted
  simp only at accepted
  simpa [arityShiftSpec] using
    replaceAppliedEnds_localSignature_exact source wire sites
      (arityShiftSpec source wire relationArguments sites newArgument) _
      result accepted fresh

/-- The operation-local wire indexed by a source occurrence is scoped at
that occurrence's exact region. -/
theorem arityShift_localScope_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel relationArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (site : Fin result.sites.sites.length) :
    result.spec.localScope
        (Fin.cast
          (arityShift_localCount_exact source wire relationArguments
            sourceSignature sites newArgument result accepted).symm site) =
      (result.sites.sites.get site).region := by
  have operationAccepted := accepted
  unfold arityShift checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  unfold checkedArgumentSites at accepted
  rw [sites.checked] at accepted
  simp only at accepted
  have sitesExact := replaceAppliedEnds_sites_exact source wire sites
    (arityShiftSpec source wire relationArguments sites newArgument) _
    result accepted
  have scopeExact := replaceAppliedEnds_localScope_exact source wire sites
    (arityShiftSpec source wire relationArguments sites newArgument) _
    result accepted
      (Fin.cast
        (arityShift_localCount_exact source wire relationArguments
          sourceSignature sites newArgument result operationAccepted).symm site)
  simpa [arityShiftSpec, sitesExact] using scopeExact

/-- At every region, arity shift retains the ordered source-local signature
block except for the acted head, then contributes the replacement head and
one fixed-signature entry for each operation-local wire scoped there. -/
theorem arityShift_localSignatures_shape
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId) :
    (result.checked.val.wiresAt (result.regionImage region)).map
        (fun targetWire => (result.checked.val.wires targetWire).sig) =
      ((source.val.wiresAt region).filter
          (fun sourceWire => decide (sourceWire ∉ [wire]))).map
          (fun sourceWire => (source.val.wires sourceWire).sig) ++
        ((Data.Finite.allFin 1).filter fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source region).map (fun _head =>
              .rel result.targetArguments) ++
        ((Data.Finite.allFin result.spec.localCount).filter fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source region).map (fun _ => newArgument) := by
  rw [result.localSignatures_decomposition]
  have removedExact :=
    arityShift_sourceRemovedWires_exact source wire newArgument result accepted
  rw [removedExact]
  congr 1
  apply List.map_congr_left
  intro fresh _member
  exact arityShift_localSignature_exact source wire sourceArguments
    sourceSignature sites newArgument result accepted fresh

/-- Every total arity-shift construction is scope-local: it removes only the
acted head and creates each fresh argument wire at its corresponding applied
site. -/
theorem arityShift_scopeLocalization
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (relationArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel relationArguments)
    (sites : AllAppliedSites source wire)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result) :
    result.ScopeLocalization := by
  unfold arityShift checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  unfold checkedArgumentSites at accepted
  rw [sites.checked] at accepted
  simp only at accepted
  let spec :=
    arityShiftSpec source wire relationArguments sites newArgument
  have valid : ReplacementValid spec :=
    arityShiftSpec_valid source wire relationArguments sourceSignature sites
      newArgument
  apply replaceAppliedEnds_scopeLocalization sites spec
    valid.removedExhausted
  · intro sourceWire removed
    have same : sourceWire = wire := by
      simpa [spec, arityShiftSpec] using removed
    subst sourceWire
    exact ConcreteDiagram.encloses_refl source.val _
  · intro fresh
    simpa [spec, arityShiftSpec] using
      (sites.sites.get fresh).head_visible
  · simpa [spec] using accepted

private structure LocalUnshiftWiresReceipt
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) where
  wires : List source.val.WireId
  exhausted :
    ∀ sourceWire, sourceWire ∈ wires →
      ∀ endpoint, endpoint ∈ (source.val.wires sourceWire).endpoints →
        endpoint.node ∈ argumentSiteNodes sites

private def localUnshiftWires?
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (position : Nat) :
    Except ArgumentError (LocalUnshiftWiresReceipt sites) := by
  let selected := sites.sites.map fun site => site.arguments[position]?
  if missing : selected.any Option.isNone then
    exact .error .invalidPosition
  else
    let locals := selected.filterMap id
    if (sites.sites.zip locals).all (fun pair =>
        (source.val.wires pair.2).scope == pair.1.region) then
      if endpointsAccepted : (sites.sites.zip locals).all (fun pair =>
          (source.val.wires pair.2).endpoints ==
            [⟨pair.1.node, .arg position⟩]) then
        exact .ok
          { wires := locals
            exhausted := by
              intro sourceWire removed endpoint incident
              have missingFalse : selected.any Option.isNone = false :=
                by
                  cases exactValue : selected.any Option.isNone with
                  | false => rfl
                  | true => simp [exactValue] at missing
              have allSome :
                  ∀ value, value ∈ selected → value.isSome := by
                intro value member
                have notNone :=
                  (List.any_eq_false.mp missingFalse) value member
                cases value <;> simp_all
              have localsLength : locals.length = selected.length := by
                apply List.filterMap_length_eq_length.mpr
                intro value member
                exact allSome value member
              have selectedLength : selected.length = sites.sites.length := by
                simp [selected]
              have lengthExact : locals.length = sites.sites.length :=
                localsLength.trans selectedLength
              have mappedMember :
                  sourceWire ∈
                    (sites.sites.zip locals).map Prod.snd := by
                rw [List.map_snd_zip (by omega)]
                exact removed
              rcases List.mem_map.mp mappedMember with
                ⟨pair, pairMember, pairExact⟩
              rcases pair with ⟨site, localWire⟩
              simp only at pairExact
              subst localWire
              have endpointsCheck :=
                (List.all_eq_true.mp endpointsAccepted)
                  (site, sourceWire) pairMember
              have endpointsExact := eq_of_beq endpointsCheck
              rw [endpointsExact] at incident
              have endpointExact := List.mem_singleton.mp incident
              have nodeExact : endpoint.node = site.node :=
                congrArg CEndpoint.node endpointExact
              unfold argumentSiteNodes
              apply List.mem_map.mpr
              exact ⟨site, (List.of_mem_zip pairMember).1,
                nodeExact.symm⟩ }
      else
        exact .error .unshiftWireNotExhausted
    else
      exact .error .unshiftWireNotLocal

/-- Remove one per-site locally scoped exhausted argument. -/
def arityUnshift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validPosition relationArguments position then
    throw .invalidPosition
  let sites ← checkedArgumentSites source wire
  let localReceipt ← localUnshiftWires? sites position
  let locals := localReceipt.wires
  let spec : ReplacementSpec source wire sites :=
    { targetArguments := eraseAt relationArguments position
      removedWires := locals
      localCount := 0
      localSignature := Fin.elim0
      localScope := Fin.elim0
      arguments := fun site =>
        existingReferences <|
          eraseAt (sites.sites.get site).arguments position }
  replaceAppliedEnds source wire sites spec (by
    intro sourceWire removed endpoint incident
    rcases List.mem_cons.mp removed with same | removedLocal
    · subst sourceWire
      exact allAppliedSites_removed_exhausted sites endpoint incident
    · exact localReceipt.exhausted sourceWire removedLocal endpoint incident)

/-- Reorder every applied argument tuple by one checked permutation. -/
def argPermute
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (permutation : List Nat) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validPermutation relationArguments.length permutation then
    throw .invalidPermutation
  let sites ← checkedArgumentSites source wire
  let spec : ReplacementSpec source wire sites :=
    { targetArguments := permute relationArguments permutation
      removedWires := []
      localCount := 0
      localSignature := Fin.elim0
      localScope := Fin.elim0
      arguments := fun site =>
        existingReferences <|
          permute (sites.sites.get site).arguments permutation }
  replaceAppliedEnds source wire sites spec (by
    intro sourceWire removed endpoint incident
    exact head_only_removed_exhausted sites sourceWire
      (by simpa [spec] using removed) endpoint incident)

/-- Argument permutation deletes exactly its acted relation head and no
ambient wire. -/
theorem argPermute_sourceRemovedWires_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (permutation : List Nat)
    (result : ArgumentResult source wire)
    (accepted : argPermute source wire permutation = .ok result) :
    result.sourceRemovedWires = [wire] := by
  unfold argPermute at accepted
  cases relationAccepted : checkedRelationArguments source wire with
  | error error =>
      rw [relationAccepted] at accepted
      contradiction
  | ok relationArguments =>
      rw [relationAccepted] at accepted
      dsimp [bind, pure, Except.instMonad, Except.bind, Except.pure] at accepted
      change
        (if !validPermutation relationArguments.length permutation then
            .error .invalidPermutation
          else do
            let sites ← checkedArgumentSites source wire
            let spec : ReplacementSpec source wire sites :=
              { targetArguments := permute relationArguments permutation
                removedWires := []
                localCount := 0
                localSignature := Fin.elim0
                localScope := Fin.elim0
                arguments := fun site =>
                  existingReferences <|
                    permute (sites.sites.get site).arguments permutation }
            replaceAppliedEnds source wire sites spec _) =
          .ok result at accepted
      cases valid : validPermutation relationArguments.length permutation with
      | false => simp [valid] at accepted
      | true =>
        simp [valid] at accepted
        cases sitesAccepted : checkedArgumentSites source wire with
        | error error =>
            rw [sitesAccepted] at accepted
            contradiction
        | ok sites =>
            rw [sitesAccepted] at accepted
            have exact :=
              replaceAppliedEnds_sourceRemovedWires_exact source wire sites
                { targetArguments := permute relationArguments permutation
                  removedWires := []
                  localCount := 0
                  localSignature := Fin.elim0
                  localScope := Fin.elim0
                  arguments := fun site =>
                    existingReferences <|
                      permute (sites.sites.get site).arguments permutation }
                _ result accepted
            simpa using exact

/-- A successful argument permutation retains the complete finite
permutation receipt checked against the acted relation arity. -/
theorem argPermute_valid_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (permutation : List Nat)
    (result : ArgumentResult source wire)
    (accepted : argPermute source wire permutation = .ok result) :
    validPermutation sourceArguments.length permutation = true := by
  unfold argPermute checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  change
    (if !validPermutation sourceArguments.length permutation then
        .error .invalidPermutation
      else do
        let sites ← checkedArgumentSites source wire
        let spec : ReplacementSpec source wire sites :=
          { targetArguments := permute sourceArguments permutation
            removedWires := []
            localCount := 0
            localSignature := Fin.elim0
            localScope := Fin.elim0
            arguments := fun site =>
              existingReferences <|
                permute (sites.sites.get site).arguments permutation }
        replaceAppliedEnds source wire sites spec _) =
      .ok result at accepted
  cases valid : validPermutation sourceArguments.length permutation with
  | false => simp [valid] at accepted
  | true => rfl

/-- A successful argument permutation retains the exact permuted relation
signature selected by the construction. -/
theorem argPermute_targetArguments_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (permutation : List Nat)
    (result : ArgumentResult source wire)
    (accepted : argPermute source wire permutation = .ok result) :
    result.targetArguments = permute sourceArguments permutation := by
  unfold argPermute checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  change
    (if !validPermutation sourceArguments.length permutation then
        .error .invalidPermutation
      else do
        let sites ← checkedArgumentSites source wire
        let spec : ReplacementSpec source wire sites :=
          { targetArguments := permute sourceArguments permutation
            removedWires := []
            localCount := 0
            localSignature := Fin.elim0
            localScope := Fin.elim0
            arguments := fun site =>
              existingReferences <|
                permute (sites.sites.get site).arguments permutation }
        replaceAppliedEnds source wire sites spec _) =
      .ok result at accepted
  cases valid : validPermutation sourceArguments.length permutation with
  | false => simp [valid] at accepted
  | true =>
    simp [valid] at accepted
    cases sitesAccepted : checkedArgumentSites source wire with
    | error error => rw [sitesAccepted] at accepted; contradiction
    | ok sites =>
      rw [sitesAccepted] at accepted
      exact replaceAppliedEnds_targetArguments_exact source wire sites
        { targetArguments := permute sourceArguments permutation
          removedWires := []
          localCount := 0
          localSignature := Fin.elim0
          localScope := Fin.elim0
          arguments := fun site =>
            existingReferences <|
              permute (sites.sites.get site).arguments permutation }
        _ result accepted

/-- A successful argument permutation retains the exact ordered attachment
tuple for every construction-owned source-site position. -/
theorem argPermute_arguments_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (permutation : List Nat)
    (result : ArgumentResult source wire)
    (accepted : argPermute source wire permutation = .ok result)
    (site : Fin result.sites.sites.length) :
    result.spec.arguments site =
      existingReferences
        (permute (result.sites.sites.get site).arguments permutation) := by
  unfold argPermute checkedRelationArguments relationArguments? at accepted
  rw [sourceSignature] at accepted
  simp only at accepted
  change
    (if !validPermutation sourceArguments.length permutation then
        .error .invalidPermutation
      else do
        let sites ← checkedArgumentSites source wire
        let spec : ReplacementSpec source wire sites :=
          { targetArguments := permute sourceArguments permutation
            removedWires := []
            localCount := 0
            localSignature := Fin.elim0
            localScope := Fin.elim0
            arguments := fun site =>
              existingReferences <|
                permute (sites.sites.get site).arguments permutation }
        replaceAppliedEnds source wire sites spec _) =
      .ok result at accepted
  cases valid : validPermutation sourceArguments.length permutation with
  | false => simp [valid] at accepted
  | true =>
    simp [valid] at accepted
    cases sitesAccepted : checkedArgumentSites source wire with
    | error error => rw [sitesAccepted] at accepted; contradiction
    | ok sites =>
      rw [sitesAccepted] at accepted
      change
        replaceAppliedEnds source wire sites
          { targetArguments := permute sourceArguments permutation
            removedWires := []
            localCount := 0
            localSignature := Fin.elim0
            localScope := Fin.elim0
            arguments := fun site =>
              existingReferences <|
                permute (sites.sites.get site).arguments permutation }
          _ = .ok result at accepted
      unfold replaceAppliedEnds at accepted
      split at accepted <;> try contradiction
      next removal _removalAccepted =>
        simp only at accepted
        split at accepted <;> try contradiction
        next checked _checkedAccepted =>
          split at accepted <;> try contradiction
          next targetSites _targetSitesAccepted =>
            have resultExact := Except.ok.inj accepted
            subst result
            rfl

/-- Argument permutation allocates no operation-local wire. -/
theorem argPermute_localCount_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (permutation : List Nat)
    (result : ArgumentResult source wire)
    (accepted : argPermute source wire permutation = .ok result) :
    result.spec.localCount = 0 := by
  unfold argPermute at accepted
  cases relationAccepted : checkedRelationArguments source wire with
  | error error =>
      rw [relationAccepted] at accepted
      contradiction
  | ok relationArguments =>
      rw [relationAccepted] at accepted
      dsimp [bind, pure, Except.instMonad, Except.bind, Except.pure] at accepted
      change
        (if !validPermutation relationArguments.length permutation then
            .error .invalidPermutation
          else do
            let sites ← checkedArgumentSites source wire
            let spec : ReplacementSpec source wire sites :=
              { targetArguments := permute relationArguments permutation
                removedWires := []
                localCount := 0
                localSignature := Fin.elim0
                localScope := Fin.elim0
                arguments := fun site =>
                  existingReferences <|
                    permute (sites.sites.get site).arguments permutation }
            replaceAppliedEnds source wire sites spec _) =
          .ok result at accepted
      cases valid : validPermutation relationArguments.length permutation with
      | false => simp [valid] at accepted
      | true =>
        simp [valid] at accepted
        cases sitesAccepted : checkedArgumentSites source wire with
        | error error =>
            rw [sitesAccepted] at accepted
            contradiction
        | ok sites =>
            rw [sitesAccepted] at accepted
            exact replaceAppliedEnds_localCount_exact source wire sites
              { targetArguments := permute relationArguments permutation
                removedWires := []
                localCount := 0
                localSignature := Fin.elim0
                localScope := Fin.elim0
                arguments := fun site =>
                  existingReferences <|
                    permute (sites.sites.get site).arguments permutation }
              _ result accepted

/-- Duplicate one position directly after itself at every applied end. -/
def argDuplicate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validPosition relationArguments position then
    throw .invalidPosition
  let sites ← checkedArgumentSites source wire
  let signature := relationArguments[position]?.getD .iota
  let spec : ReplacementSpec source wire sites :=
    { targetArguments :=
        insertAt relationArguments (position + 1) signature
      removedWires := []
      localCount := 0
      localSignature := Fin.elim0
      localScope := Fin.elim0
      arguments := fun site =>
        existingReferences <|
          insertAt (sites.sites.get site).arguments (position + 1)
            (((sites.sites.get site).arguments[position]?).getD wire) }
  replaceAppliedEnds source wire sites spec (by
    intro sourceWire removed endpoint incident
    exact head_only_removed_exhausted sites sourceWire
      (by simpa [spec] using removed) endpoint incident)

/-- Contract equal adjacent positions attached to the same wire at every end. -/
def argContract
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validPosition relationArguments position ||
      !validPosition relationArguments (position + 1) then
    throw .invalidPosition
  if relationArguments[position]? != relationArguments[position + 1]? then
    throw .unequalAdjacentSignatures
  let sites ← checkedArgumentSites source wire
  if !(sites.sites.all fun site =>
      site.arguments[position]? = site.arguments[position + 1]?) then
    throw .unequalAdjacentAttachments
  let spec : ReplacementSpec source wire sites :=
    { targetArguments := eraseAt relationArguments (position + 1)
      removedWires := []
      localCount := 0
      localSignature := Fin.elim0
      localScope := Fin.elim0
      arguments := fun site =>
        existingReferences <|
          eraseAt (sites.sites.get site).arguments (position + 1) }
  replaceAppliedEnds source wire sites spec (by
    intro sourceWire removed endpoint incident
    exact head_only_removed_exhausted sites sourceWire
      (by simpa [spec] using removed) endpoint incident)

/-- Drop one argument position at every applied end. -/
def argDrop
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validPosition relationArguments position then
    throw .invalidPosition
  let sites ← checkedArgumentSites source wire
  let spec : ReplacementSpec source wire sites :=
    { targetArguments := eraseAt relationArguments position
      removedWires := []
      localCount := 0
      localSignature := Fin.elim0
      localScope := Fin.elim0
      arguments := fun site =>
        existingReferences <|
          eraseAt (sites.sites.get site).arguments position }
  replaceAppliedEnds source wire sites spec (by
    intro sourceWire removed endpoint incident
    exact head_only_removed_exhausted sites sourceWire
      (by simpa [spec] using removed) endpoint incident)

/-- Argument drop deletes exactly its acted relation head and no ambient
wire. -/
theorem argDrop_sourceRemovedWires_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (result : ArgumentResult source wire)
    (accepted : argDrop source wire position = .ok result) :
  result.sourceRemovedWires = [wire] := by
  unfold argDrop at accepted
  cases relationAccepted : checkedRelationArguments source wire with
  | error error =>
      rw [relationAccepted] at accepted
      contradiction
  | ok relationArguments =>
      rw [relationAccepted] at accepted
      change
        (if !validPosition relationArguments position then
            Except.error ArgumentError.invalidPosition
          else do
            let sites ← checkedArgumentSites source wire
            let spec : ReplacementSpec source wire sites :=
              { targetArguments := eraseAt relationArguments position
                removedWires := []
                localCount := 0
                localSignature := Fin.elim0
                localScope := Fin.elim0
                arguments := fun site =>
                  existingReferences <|
                    eraseAt (sites.sites.get site).arguments position }
            replaceAppliedEnds source wire sites spec _) =
          .ok result at accepted
      cases valid : validPosition relationArguments position with
      | false => simp [valid] at accepted
      | true =>
        simp [valid] at accepted
        cases sitesAccepted : checkedArgumentSites source wire with
        | error error =>
            rw [sitesAccepted] at accepted
            contradiction
        | ok sites =>
            rw [sitesAccepted] at accepted
            have exact :=
              replaceAppliedEnds_sourceRemovedWires_exact source wire sites
                { targetArguments := eraseAt relationArguments position
                  removedWires := []
                  localCount := 0
                  localSignature := Fin.elim0
                  localScope := Fin.elim0
                  arguments := fun site =>
                    existingReferences <|
                      eraseAt (sites.sites.get site).arguments position }
                _ result accepted
            simpa using exact

/-- Argument drop allocates no operation-local wire. -/
theorem argDrop_localCount_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (result : ArgumentResult source wire)
    (accepted : argDrop source wire position = .ok result) :
    result.spec.localCount = 0 := by
  unfold argDrop at accepted
  cases relationAccepted : checkedRelationArguments source wire with
  | error error =>
      rw [relationAccepted] at accepted
      contradiction
  | ok relationArguments =>
      rw [relationAccepted] at accepted
      change
        (if !validPosition relationArguments position then
            .error .invalidPosition
          else do
            let sites ← checkedArgumentSites source wire
            let spec : ReplacementSpec source wire sites :=
              { targetArguments := eraseAt relationArguments position
                removedWires := []
                localCount := 0
                localSignature := Fin.elim0
                localScope := Fin.elim0
                arguments := fun site =>
                  existingReferences <|
                    eraseAt (sites.sites.get site).arguments position }
            replaceAppliedEnds source wire sites spec _) =
          .ok result at accepted
      cases valid : validPosition relationArguments position with
      | false => simp [valid] at accepted
      | true =>
        simp [valid] at accepted
        cases sitesAccepted : checkedArgumentSites source wire with
        | error error =>
            rw [sitesAccepted] at accepted
            contradiction
        | ok sites =>
            rw [sitesAccepted] at accepted
            exact replaceAppliedEnds_localCount_exact source wire sites
              { targetArguments := eraseAt relationArguments position
                removedWires := []
                localCount := 0
                localSignature := Fin.elim0
                localScope := Fin.elim0
                arguments := fun site =>
                  existingReferences <|
                    eraseAt (sites.sites.get site).arguments position }
              _ result accepted

/-- Insert one caller-selected visible attachment at every applied end. -/
def argExtend
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId) :
    Except ArgumentError (ArgumentResult source wire) :=
  match checkedRelationArguments source wire with
  | .error error => .error error
  | .ok relationArguments =>
      if !validInsertionPosition relationArguments position then
        .error .invalidPosition
      else
        match checkedArgumentSites source wire with
        | .error error => .error error
        | .ok sites =>
            if attachments.length != sites.sites.length then
              .error .attachmentCoverage
            else if !(attachments.all fun attachment =>
                (source.val.wires attachment).sig == newArgument) then
              .error .attachmentSignature
            else if !((sites.sites.zip attachments).all fun pair =>
                source.val.Encloses
                  (source.val.wires pair.2).scope pair.1.region) then
              .error .attachmentInvisible
            else
              let spec : ReplacementSpec source wire sites :=
                { targetArguments :=
                    insertAt relationArguments position newArgument
                  removedWires := []
                  localCount := 0
                  localSignature := Fin.elim0
                  localScope := Fin.elim0
                  arguments := fun site =>
                    existingReferences <|
                      insertAt (sites.sites.get site).arguments position
                        ((attachments[site.val]?).getD wire) }
              replaceAppliedEnds source wire sites spec (by
                intro sourceWire removed endpoint incident
                exact head_only_removed_exhausted sites sourceWire
                  (by simpa [spec] using removed) endpoint incident)

/-- Argument extension deletes exactly its acted relation head and no ambient
wire. -/
theorem argExtend_sourceRemovedWires_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId)
    (result : ArgumentResult source wire)
    (accepted :
      argExtend source wire position newArgument attachments = .ok result) :
    result.sourceRemovedWires = [wire] := by
  unfold argExtend at accepted
  cases relationAccepted : checkedRelationArguments source wire with
  | error error =>
      rw [relationAccepted] at accepted
      contradiction
  | ok relationArguments =>
      rw [relationAccepted] at accepted
      change
        (if !validInsertionPosition relationArguments position then
            .error .invalidPosition
          else
            match checkedArgumentSites source wire with
            | .error error => Except.error error
            | .ok sites =>
                if attachments.length != sites.sites.length then
                  Except.error ArgumentError.attachmentCoverage
                else if !(attachments.all fun attachment =>
                    (source.val.wires attachment).sig == newArgument) then
                  Except.error ArgumentError.attachmentSignature
                else if !((sites.sites.zip attachments).all fun pair =>
                    source.val.Encloses
                      (source.val.wires pair.2).scope pair.1.region) then
                  Except.error ArgumentError.attachmentInvisible
                else
                  replaceAppliedEnds source wire sites
                    { targetArguments :=
                        insertAt relationArguments position newArgument
                      removedWires := []
                      localCount := 0
                      localSignature := Fin.elim0
                      localScope := Fin.elim0
                      arguments := fun site =>
                        existingReferences <|
                          insertAt (sites.sites.get site).arguments position
                            ((attachments[site.val]?).getD wire) }
                    _) =
          .ok result at accepted
      cases valid : validInsertionPosition relationArguments position with
      | false => simp [valid] at accepted
      | true =>
        simp [valid] at accepted
        cases sitesAccepted : checkedArgumentSites source wire with
        | error error =>
            rw [sitesAccepted] at accepted
            contradiction
        | ok sites =>
            rw [sitesAccepted] at accepted
            split at accepted <;> try contradiction
            next coverage _ =>
              split at accepted <;> try contradiction
              next signatures _ =>
                split at accepted <;> try contradiction
                next visible _ =>
                  split at accepted <;> try contradiction
                  next scope _ =>
                    have exact :=
                      replaceAppliedEnds_sourceRemovedWires_exact source wire
                        coverage
                        { targetArguments :=
                            insertAt relationArguments position newArgument
                          removedWires := []
                          localCount := 0
                          localSignature := Fin.elim0
                          localScope := Fin.elim0
                          arguments := fun site =>
                            existingReferences <|
                              insertAt (coverage.sites.get site).arguments
                                position ((attachments[site.val]?).getD wire) }
                        _ result accepted
                    simpa using exact

/-- Argument extension allocates no operation-local wire. -/
theorem argExtend_localCount_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId)
    (result : ArgumentResult source wire)
    (accepted :
      argExtend source wire position newArgument attachments = .ok result) :
    result.spec.localCount = 0 := by
  unfold argExtend at accepted
  cases relationAccepted : checkedRelationArguments source wire with
  | error error =>
      rw [relationAccepted] at accepted
      contradiction
  | ok relationArguments =>
      rw [relationAccepted] at accepted
      change
        (if !validInsertionPosition relationArguments position then
            Except.error ArgumentError.invalidPosition
          else
            match checkedArgumentSites source wire with
            | .error error => Except.error error
            | .ok sites =>
                if attachments.length != sites.sites.length then
                  Except.error ArgumentError.attachmentCoverage
                else if !(attachments.all fun attachment =>
                    (source.val.wires attachment).sig == newArgument) then
                  Except.error ArgumentError.attachmentSignature
                else if !((sites.sites.zip attachments).all fun pair =>
                    source.val.Encloses
                      (source.val.wires pair.2).scope pair.1.region) then
                  Except.error ArgumentError.attachmentInvisible
                else
                  replaceAppliedEnds source wire sites
                    { targetArguments :=
                        insertAt relationArguments position newArgument
                      removedWires := []
                      localCount := 0
                      localSignature := Fin.elim0
                      localScope := Fin.elim0
                      arguments := fun site =>
                        existingReferences <|
                          insertAt (sites.sites.get site).arguments position
                            ((attachments[site.val]?).getD wire) }
                    _) =
          .ok result at accepted
      cases valid : validInsertionPosition relationArguments position with
      | false => simp [valid] at accepted
      | true =>
        simp [valid] at accepted
        cases sitesAccepted : checkedArgumentSites source wire with
        | error error =>
            rw [sitesAccepted] at accepted
            contradiction
        | ok sites =>
            rw [sitesAccepted] at accepted
            split at accepted <;> try contradiction
            next coverage _ =>
              split at accepted <;> try contradiction
              next signatures _ =>
                split at accepted <;> try contradiction
                next visible _ =>
                  split at accepted <;> try contradiction
                  next scope _ =>
                    exact replaceAppliedEnds_localCount_exact source wire
                      coverage
                      { targetArguments :=
                          insertAt relationArguments position newArgument
                        removedWires := []
                        localCount := 0
                        localSignature := Fin.elim0
                        localScope := Fin.elim0
                        arguments := fun site =>
                          existingReferences <|
                            insertAt (coverage.sites.get site).arguments
                              position ((attachments[site.val]?).getD wire) }
                      _ result accepted

end ConcreteWirePrimitive

end VisualProof
