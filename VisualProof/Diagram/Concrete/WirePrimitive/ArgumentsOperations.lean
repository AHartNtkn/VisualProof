import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCommonCore

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

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

/-- Insert one caller-selected visible attachment at every applied end. -/
def argExtend
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validInsertionPosition relationArguments position then
    throw .invalidPosition
  let sites ← checkedArgumentSites source wire
  if attachments.length != sites.sites.length then
    throw .attachmentCoverage
  if !(attachments.all fun attachment =>
      (source.val.wires attachment).sig == newArgument) then
    throw .attachmentSignature
  if !((sites.sites.zip attachments).all fun pair =>
      source.val.Encloses
        (source.val.wires pair.2).scope pair.1.region) then
    throw .attachmentInvisible
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

end ConcreteWirePrimitive

end VisualProof
