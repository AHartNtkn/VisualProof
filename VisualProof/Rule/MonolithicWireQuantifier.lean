import VisualProof.Rule.MonolithicWireQuantifierReconstructionIso

namespace VisualProof

universe u

namespace MonolithicWireQuantifier

open Internal

/-- Opaque accepted strongest relation-join transformation. -/
structure AppliedMonolithicRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source) where
  private mk ::
  target : CheckedDiagram definitions
  applications : List source.val.NodeId
  private checked :
    RelationJoinReceipt source input.orientation input.wire input.content
      input.parameters target applications

/-- Opaque accepted strongest relation-sever transformation. -/
structure AppliedMonolithicRelationSever
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationSeverInput source) where
  private mk ::
  target : CheckedDiagram definitions
  private polarity :
    CheckedSeverPolarity source input.orientation input.scope
  private concrete :
    RelationSeverConcreteReceipt source input.orientation input.scope
      input.pattern input.occurrences target
  private inverseInput : MonolithicRelationJoinInput target
  private inverseApplied :
    AppliedMonolithicRelationJoin target inverseInput
  private inversePlainFinalExact :
    inverseApplied.checked.result.plainFinal = concrete.inverse.plainFinal

namespace AppliedMonolithicRelationJoin

/-- The concrete strongest-form construction retained by the accepted receipt. -/
def concreteResult
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    ConcreteWireQuantifier.RelationJoinResult source input.wire input.content
      input.parameters :=
  applied.checked.result

/-- The accepted join landing before the concrete result's single eager
identity-normalization pass.  The primitive compiler targets this raw carrier;
normalization remains derived state rather than a durable primitive step. -/
def plainFinal
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    CheckedDiagram definitions :=
  applied.concreteResult.plainFinal

/-- Accepted strongest joins for the same checked input retain the same
concrete result because both receipts witness the output of the same total
checker call. -/
theorem concreteResult_unique
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (left right : AppliedMonolithicRelationJoin source input) :
    left.concreteResult = right.concreteResult := by
  apply Except.ok.inj
  exact left.checked.accepted.symm.trans right.checked.accepted

/-- Consequently, the raw accepted join carrier is unique for a checked
input even when callers hold distinct opaque receipt values. -/
theorem plainFinal_unique
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (left right : AppliedMonolithicRelationJoin source input) :
    left.plainFinal = right.plainFinal :=
  congrArg ConcreteWireQuantifier.RelationJoinResult.plainFinal
    (left.concreteResult_unique right)

end AppliedMonolithicRelationJoin

namespace AppliedMonolithicRelationSever

/--
The exact virtual join already checked as part of a strongest-form sever
receipt.  This is exposed only so the authoring-layer primitive compiler can
reverse that checked construction; the monolithic action remains absent from
the durable proof-step language.
-/
def inverseJoinInput
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (applied : AppliedMonolithicRelationSever source input) :
    MonolithicRelationJoinInput applied.target :=
  applied.inverseInput

/--
The already-accepted virtual inverse join retained by a strongest-form sever.
The primitive compiler consumes this receipt directly, so sever compilation
does not re-run or strengthen the monolithic acceptance boundary.
-/
def inverseJoinApplied
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (applied : AppliedMonolithicRelationSever source input) :
    AppliedMonolithicRelationJoin applied.target applied.inverseJoinInput :=
  applied.inverseApplied

/-- The unnormalized checked inverse-join landing reconstructed by the sever
receipt before the inverse join's final identity normalization. -/
def inversePlainFinal
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (applied : AppliedMonolithicRelationSever source input) :
    CheckedDiagram definitions :=
  applied.concrete.inverse.plainFinal

/-- The raw carrier exposed by the retained virtual join is exactly the raw
inverse landing stored by the sever receipt. -/
theorem inverseJoinPlainFinal_eq_inversePlainFinal
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (applied : AppliedMonolithicRelationSever source input) :
    applied.inverseJoinApplied.plainFinal = applied.inversePlainFinal := by
  exact applied.inversePlainFinalExact

/-- Total construction-owned reconstruction from the checked virtual inverse
landing to the original sever source.  Compiler reversal composes against
this witness and never rediscovers the graph. -/
def reconstructionIso
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (applied : AppliedMonolithicRelationSever source input) :
    ConcreteIso applied.inversePlainFinal.val source.val :=
  applied.concrete.constructionIso.symm

end AppliedMonolithicRelationSever

namespace AppliedMonolithicRelationJoin

/-- The canonical checked carrier obtained by normalizing the raw accepted
join landing. -/
def normalizedPlainFinal
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    CheckedDiagram definitions :=
  (ConcreteDiagram.normalizeIdentities applied.plainFinal).target

/-- The monolithic public target is exactly the canonical normalization of its
raw `plainFinal` carrier. -/
theorem normalizedPlainFinal_eq_target
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    applied.normalizedPlainFinal = applied.target := by
  obtain ⟨_steps, normalization, _semantic, _applications,
      normalizationExact, checkedExact⟩ :=
    applied.concreteResult.trace_complete
  rw [normalizationExact] at checkedExact
  exact checkedExact.trans applied.checked.targetExact.symm

/-- The public target is exactly the concrete strongest-form result. -/
theorem target_eq_concreteResult
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    applied.target = applied.concreteResult.checked :=
  applied.checked.targetExact

/-- Every endpoint of the accepted source relation is an applied atom head. -/
theorem endpoint_applied
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires input.wire).endpoints) :
    endpoint.port = .head ∧
      ∃ region,
        source.val.nodes endpoint.node =
          .atom region applied.concreteResult.args :=
  applied.concreteResult.endpoint_applied endpoint member

private theorem sourceSites_exists
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    ∃ all,
      WirePrimitive.checkAllAppliedSites source input.wire = some all := by
  apply WirePrimitive.checkAllAppliedSites_complete
  intro endpoint member
  obtain ⟨head, region, nodeData⟩ :=
    applied.endpoint_applied endpoint member
  exact ⟨head, region, applied.concreteResult.args, nodeData⟩

/--
The exhaustive checker-owned source sites implied by an accepted strongest
join.  This is derived from checked concrete incidence, not retained as a
second authority in the monolithic receipt.
-/
def sourceSites
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    WirePrimitive.AllAppliedSites source input.wire :=
  match accepted :
      WirePrimitive.checkAllAppliedSites source input.wire with
  | some sites => sites
  | none => by
      exfalso
      obtain ⟨sites, complete⟩ := applied.sourceSites_exists
      rw [accepted] at complete
      contradiction

/-- The executable exhaustive-site checker accepts the derived source sites. -/
theorem sourceSites_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    WirePrimitive.checkAllAppliedSites source input.wire =
      some applied.sourceSites :=
  by
    unfold sourceSites
    split
    next sites accepted => exact accepted
    next accepted =>
      obtain ⟨sites, complete⟩ := applied.sourceSites_exists
      rw [accepted] at complete
      contradiction

/-- The checker-owned site compilation at the dying relation's scope. -/
def sourceSite
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    SiteCompilation source (source.val.wires input.wire).scope :=
  applied.checked.polarity.compiled

/-- The source-site compiler returned the exact polarity receipt used here. -/
theorem sourceSite_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    compileSite? source (source.val.wires input.wire).scope =
      some applied.sourceSite :=
  applied.checked.polarity.compiledAccepted

/-- Exact enclosing-scope evidence for every ordered ambient parameter. -/
theorem parameter_encloses
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input)
    (position : Fin input.parameters.length) :
    source.val.Encloses
      (source.val.wires (input.parameters.get position)).scope
      (source.val.wires input.wire).scope :=
  applied.checked.parameterScopes position

/-- The exact relation argument signature accepted by the monolithic checker. -/
def arguments
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    List Sig :=
  applied.checked.arguments

theorem sourceSignature
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (source.val.wires input.wire).sig = .rel applied.arguments :=
  applied.checked.sourceSignature

theorem boundaryLength
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    input.content.val.boundary.length =
      applied.arguments.length + input.parameters.length :=
  applied.checked.boundaryLength

theorem formalSignatures
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (input.content.val.boundary.take applied.arguments.length).map
        (fun wire => (input.content.val.diagram.wires wire).sig) =
      applied.arguments :=
  applied.checked.formalSignatures

theorem parameterSignatures
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (input.content.val.boundary.drop applied.arguments.length).map
        (fun wire => (input.content.val.diagram.wires wire).sig) =
      input.parameters.map (fun wire => (source.val.wires wire).sig) :=
  applied.checked.parameterSignatures

/-- The consumed relation head is not also an ambient parameter. -/
theorem live_not_parameter
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    input.wire ∉ input.parameters :=
  applied.checked.liveNotParameter

/--
The exact checked open-content compilation retained by an accepted strongest
join.  The authoring compiler may inspect this structural receipt; primitive
checkers still receive only their own local inputs.
-/
def contentCompilation
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    OpenCompilation input.content :=
  applied.checked.contentCompilation.compilation

/-- The executable open compiler returned that exact structural receipt. -/
theorem contentCompilation_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    compileOpen input.content = some applied.contentCompilation :=
  applied.checked.contentCompilation.accepted

end AppliedMonolithicRelationJoin

private def requireSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except MonolithicWireQuantifierError
      (CheckedSeverPolarity source orientation scope) := by
  match accepted : compileSite? source scope with
  | none => exact .error .occurrenceOutsideScope
  | some compiled =>
      if legal : severPolarityLegal orientation
          compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, accepted, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .severRequiresPositive
          | .backward => .severBackwardRequiresNegative

private def requireJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except MonolithicWireQuantifierError
      (CheckedJoinPolarity source orientation scope) := by
  match accepted : compileSite? source scope with
  | none => exact .error .occurrenceOutsideScope
  | some compiled =>
      if legal : joinPolarityLegal orientation
          compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, accepted, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .joinRequiresNegative
          | .backward => .joinBackwardRequiresPositive

private def validateOccurrence
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (first : ContentOccurrence source pattern)
    (content : ContentOccurrence source pattern) :
    Except MonolithicWireQuantifierError
      (CheckedOccurrence scope first content) := by
  match WireQuantifierSemantics.checkRelationSeverOccurrence
      content.selection content.occurrence with
  | .error error => exact .error (.extractionRejected error)
  | .ok extraction =>
      if !formalBoundaryValid content then
        exact .error .formalNotOnBoundary
      else if contained :
          source.val.Encloses scope content.selection.region then
        if boundaryExact :
            content.occurrence.boundaryAttachments =
              content.formals ++ content.parameters then
          if formalSigsExact :
              first.formalSigs = content.formalSigs then
            if parametersExact :
                first.parameters = content.parameters then
              if positionsExact :
                  first.formalBoundaryPositions? =
                    content.formalBoundaryPositions? then
                exact .ok
                  { extraction := extraction
                    boundaryExact := boundaryExact
                    contained := contained
                    parametersExact := parametersExact.symm }
              else
                exact .error .contentMismatch
            else
              exact .error .parameterMismatch
          else
            exact .error .formalSignatureMismatch
        else
          exact .error .contentMismatch
      else
        exact .error .occurrenceOutsideScope

private def validateOccurrences
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (first : ContentOccurrence source pattern) :
    (contents : List (ContentOccurrence source pattern)) →
      Except MonolithicWireQuantifierError
        (CheckedOccurrenceList scope first contents)
  | [] => .ok .nil
  | content :: rest => do
      let checked ← validateOccurrence scope first content
      let tail ← validateOccurrences scope first rest
      pure (.cons checked tail)

private def validateRelationSever
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (scope : source.val.RegionId)
    (pattern : CheckedOpenDiagram definitions)
    (occurrences : List (ContentOccurrence source pattern)) :
    Except MonolithicWireQuantifierError
      (CheckedSeverPolarity source orientation scope ×
        CheckedOccurrences scope occurrences) := by
  let polarityResult := requireSeverPolarity source orientation scope
  match occurrences with
  | [] => exact .error .emptyOccurrenceList
  | first :: rest =>
      match polarityResult with
      | .error error => exact .error error
      | .ok polarity => exact do
          let extractions ←
            validateOccurrences scope first (first :: rest)
          if disjoint :
              pairwiseDisjoint (first :: rest) = true then
            if parametersAccepted :
                parametersEnclose source scope first.parameters = true then
              pure
                (polarity,
                  { first := first
                    rest := rest
                    contentsExact := rfl
                    entries := extractions
                    disjoint := disjoint
                    parameterScopes :=
                      parametersEnclose_of_true source scope first.parameters
                        parametersAccepted })
            else
              throw .parameterOutsideScope
          else
            throw .occurrencesOverlap

private def validateRelationJoin
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    Except MonolithicWireQuantifierError
      (CheckedRelationJoin source orientation wire content parameters) := do
  let relation := source.val.wires wire
  let signatureData ←
    match sourceSignature : relation.sig with
    | .iota => throw .expectedRelation
    | .rel args =>
        pure
          (⟨args, sourceSignature⟩ :
            { arguments : List Sig // relation.sig = .rel arguments })
  let args := signatureData.val
  let polarity ← requireJoinPolarity source orientation relation.scope
  let contentCompilation ←
    match accepted : compileOpen content with
    | none => throw .contentCompilationFailed
    | some compilation =>
        pure
          { compilation := compilation
            accepted := accepted }
  let liveNotParameter ←
    if liveParameter : wire ∈ parameters then
      (throw .dyingWireIsParameter :
        Except MonolithicWireQuantifierError (PLift (wire ∉ parameters)))
    else
      pure ⟨liveParameter⟩
  let contentSigs := boundarySigs content
  let split ←
    match splitAccepted : splitAt? args.length contentSigs with
    | none => throw .boundaryTooShort
    | some split =>
        pure
          (⟨split, splitAccepted⟩ :
            { split : List Sig × List Sig //
              splitAt? args.length contentSigs = some split })
  let formalExact ←
    if exact : split.val.1 = args then
      (pure ⟨exact⟩ :
        Except MonolithicWireQuantifierError
          (PLift (split.val.1 = args)))
    else
      (throw .boundarySignatureMismatch :
        Except MonolithicWireQuantifierError
          (PLift (split.val.1 = args)))
  let parameterLengthExact ←
    if exact : split.val.2.length = parameters.length then
      (pure ⟨exact⟩ :
        Except MonolithicWireQuantifierError
          (PLift (split.val.2.length = parameters.length)))
    else
      (throw .parameterMismatch :
        Except MonolithicWireQuantifierError
          (PLift (split.val.2.length = parameters.length)))
  let parameterSigs :=
    parameters.map (fun parameter => (source.val.wires parameter).sig)
  let parameterExact ←
    if exact : split.val.2 = parameterSigs then
      (pure ⟨exact⟩ :
        Except MonolithicWireQuantifierError
          (PLift (split.val.2 = parameterSigs)))
    else
      (throw .parameterMismatch :
        Except MonolithicWireQuantifierError
          (PLift (split.val.2 = parameterSigs)))
  have splitExact :
      (contentSigs.take args.length, contentSigs.drop args.length) =
        split.val := by
    have splitAccepted := split.property
    unfold splitAt? at splitAccepted
    split at splitAccepted
    · exact Option.some.inj splitAccepted
    · simp at splitAccepted
  if accepted :
      parametersEnclose source relation.scope parameters = true then
    let applications ←
      match collectApplications? source wire args with
      | none => throw .nonAppliedEndpoint
      | some applications => pure applications
    pure
      { arguments := args
        sourceSignature := signatureData.property
        boundaryLength := by
          have dropExact :=
            congrArg (fun parts => parts.2.length) splitExact
          have dropLength :
              contentSigs.length - args.length = parameters.length := by
            simpa [List.length_drop] using
              dropExact.trans parameterLengthExact.down
          have argsBound : args.length ≤ contentSigs.length := by
            have splitAccepted := split.property
            unfold splitAt? at splitAccepted
            split at splitAccepted
            · assumption
            · simp at splitAccepted
          have contentLength :
              contentSigs.length =
                args.length + parameters.length := by
            omega
          simpa [contentSigs, boundarySigs] using contentLength
        formalSignatures := by
          have exact :=
            (congrArg Prod.fst splitExact).trans formalExact.down
          simpa [contentSigs, boundarySigs, List.map_take] using exact
        parameterSignatures := by
          have exact :=
            (congrArg Prod.snd splitExact).trans parameterExact.down
          simpa [contentSigs, boundarySigs, parameterSigs,
            List.map_drop] using exact
        liveNotParameter := liveNotParameter.down
        polarity := polarity
        applications := applications.map (·.node)
        contentCompilation := contentCompilation
        parameterScopes :=
          parametersEnclose_of_true source relation.scope parameters accepted }
  else
    throw .parameterOutsideScope

/--
Validate and apply one strongest sever.  All structure is computed by the
concrete owner; callers cannot supply a target or a semantic certificate.
-/
def applyMonolithicRelationSever
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationSeverInput source) :
    Except MonolithicWireQuantifierError
      (AppliedMonolithicRelationSever source input) := by
  match validateRelationSever input.orientation input.scope input.pattern
      input.occurrences with
  | .error error => exact .error error
  | .ok validated =>
      let polarity := validated.1
      let extractions := validated.2
      let sites :=
        extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site
      match accepted :
          ConcreteWireQuantifier.severRelation source input.scope sites with
      | .error error => exact .error (.concreteRejected error)
      | .ok result =>
          match parametersAccepted :
              extractions.first.parameters.mapM result.wireImage? with
          | none => exact .error .parameterTransportFailed
          | some parameters =>
              match validateRelationJoin
                  (oppositeOrientation input.orientation)
                  result.relationWire input.pattern parameters with
              | .error _ => exact .error .inverseRelationJoinRejected
              | .ok inverseChecked =>
                  match inverseAccepted :
                      ConcreteWireQuantifier.joinRelation result.checked
                        result.relationWire input.pattern parameters with
                  | .error _ =>
                      exact .error .inverseRelationJoinRejected
                  | .ok inverse =>
                      exact .ok
                        (AppliedMonolithicRelationSever.mk
                          result.checked polarity
                          { extractions := extractions
                            result := result
                            accepted := accepted
                            targetExact := rfl
                            parameters := parameters
                            parametersAccepted := parametersAccepted
                            inverseChecked := inverseChecked
                            inverse := inverse
                            inverseAccepted := inverseAccepted
                            inverseStepsExact := by
                              calc
                                inverse.steps.map
                                      ConcreteWireQuantifier.RelationJoinStep.application =
                                    inverse.applications :=
                                  inverse.steps_application_order
                                _ = result.atoms := by
                                  rw [inverse.applications_storage_order]
                                  exact
                                    result.relationApplications_storage_order }
                          { orientation :=
                              oppositeOrientation input.orientation
                            wire := result.relationWire
                            content := input.pattern
                            parameters := parameters }
                          (AppliedMonolithicRelationJoin.mk
                            inverse.checked inverse.applications
                            { arguments := inverseChecked.arguments
                              sourceSignature :=
                                inverseChecked.sourceSignature
                              boundaryLength :=
                                inverseChecked.boundaryLength
                              formalSignatures :=
                                inverseChecked.formalSignatures
                              parameterSignatures :=
                                inverseChecked.parameterSignatures
                              liveNotParameter :=
                                inverseChecked.liveNotParameter
                              polarity := inverseChecked.polarity
                              contentCompilation :=
                                inverseChecked.contentCompilation
                              result := inverse
                              accepted := inverseAccepted
                              targetExact := rfl
                              applicationsExact := rfl
                              parameterScopes :=
                                inverseChecked.parameterScopes })
                          rfl)

/--
Validate and apply one strongest join.  Relation joining consumes every
endpoint; no subset of applications is accepted.
-/
def applyMonolithicRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source) :
    Except MonolithicWireQuantifierError
      (AppliedMonolithicRelationJoin source input) := by
  match validateRelationJoin input.orientation input.wire input.content
      input.parameters with
  | .error error => exact .error error
  | .ok validated =>
      match accepted :
          ConcreteWireQuantifier.joinRelation source input.wire input.content
            input.parameters with
      | .error error => exact .error (.concreteRejected error)
      | .ok result =>
          exact .ok
            (AppliedMonolithicRelationJoin.mk
              result.checked result.applications
              { arguments := validated.arguments
                sourceSignature := validated.sourceSignature
                boundaryLength := validated.boundaryLength
                formalSignatures := validated.formalSignatures
                parameterSignatures := validated.parameterSignatures
                liveNotParameter := validated.liveNotParameter
                polarity := validated.polarity
                contentCompilation := validated.contentCompilation
                result := result
                accepted := accepted
                targetExact := rfl
                applicationsExact := rfl
                parameterScopes := validated.parameterScopes })

/--
Relation-content abstraction is sound in the direction selected by the
checker-owned sever polarity. The accepted receipt contains a checked inverse
join and its construction-owned reconstruction isomorphism; callers supply no
semantic evidence.
-/
theorem relation_sever_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (scope : source.val.RegionId)
    (pattern : CheckedOpenDiagram definitions)
    (occurrences : List (ContentOccurrence source pattern))
    (applied :
      AppliedMonolithicRelationSever source
        { orientation := orientation
          scope := scope
          pattern := pattern
          occurrences := occurrences })
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  let checked := applied.concrete
  obtain ⟨_relationFamily, _relationLaw, sound⟩ :=
    ConcreteWireQuantifier.RelationSeverInsertionSemantics.inverseJoinDenotes
      checked.inverse
        checked.inverseChecked.contentCompilation.compilation
        checked.inverseChecked.polarity.compiled
        checked.inverseChecked.parameterScopes checked.constructionIso.symm
        model definitionEnv
  rw [checked.targetExact]
  cases orientation with
  | forward =>
      have even :
          checked.inverseChecked.polarity.compiled.frame.context.cutDepth %
              2 =
            0 :=
        of_decide_eq_true (by
          simpa [oppositeOrientation, joinPolarityLegal] using
            checked.inverseChecked.polarity.legal)
      exact sound.1 even
  | backward =>
      have odd :
          checked.inverseChecked.polarity.compiled.frame.context.cutDepth %
              2 =
            1 :=
        of_decide_eq_true (by
          simpa [oppositeOrientation, joinPolarityLegal] using
            checked.inverseChecked.polarity.legal)
      exact sound.2 odd

/--
Relation-content grounding is sound in the direction selected by the
checker-owned polarity receipt.
-/
theorem relation_join_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (applied :
      AppliedMonolithicRelationJoin source
        { orientation := orientation
          wire := wire
          content := content
          parameters := parameters })
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  let checked := applied.checked
  have sound :=
    checked.result.denotes checked.contentCompilation.compilation
      checked.polarity.compiled model definitionEnv checked.parameterScopes
  rw [checked.targetExact]
  cases orientation with
  | forward =>
      have odd :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 1 :=
        of_decide_eq_true (by
          simpa [joinPolarityLegal] using checked.polarity.legal)
      exact sound.2 odd
  | backward =>
      have even :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 0 :=
        of_decide_eq_true (by
          simpa [joinPolarityLegal] using checked.polarity.legal)
      exact sound.1 even

end MonolithicWireQuantifier

export MonolithicWireQuantifier
  (ContentOccurrence MonolithicRelationSeverInput
    MonolithicRelationJoinInput MonolithicWireQuantifierError
    AppliedMonolithicRelationSever AppliedMonolithicRelationJoin
    applyMonolithicRelationSever applyMonolithicRelationJoin
    relation_sever_sound relation_join_sound)

end VisualProof
