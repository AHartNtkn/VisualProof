import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.WireQuantifierRelationSever
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoin
import VisualProof.Diagram.Concrete.WireQuantifierIota
import VisualProof.Diagram.Concrete.WireQuantifierSemantics
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinSemantics
import VisualProof.Rule.Structural

namespace VisualProof

universe u

namespace WireQuantifier

/-- Stable refusal outcomes of the strongest wire-quantifier checker. -/
inductive WireQuantifierError
  | expectedIota
  | expectedRelation
  | duplicateEndpoint
  | endpointNotOnWire
  | incomparableScopes
  | severRequiresPositive
  | severBackwardRequiresNegative
  | joinRequiresNegative
  | joinBackwardRequiresPositive
  | emptyOccurrenceList
  | extractionRejected (error : ExtractionError)
  | occurrenceOutsideScope
  | occurrencesOverlap
  | formalNotOnBoundary
  | formalSignatureMismatch
  | contentMismatch
  | parameterMismatch
  | parameterOutsideScope
  | dyingWireIsParameter
  | boundaryTooShort
  | boundarySignatureMismatch
  | nonAppliedEndpoint
  | repeatedApplication
  | applicationSignatureMismatch
  | missingApplicationArgument
  | applicationOutsideScope
  | contentCompilationFailed
  | concreteRejected (error : ConcreteWireQuantifier.Error)
  deriving Repr, DecidableEq

/--
One explicitly designated exact occurrence.

The occurrence owns its extent and canonical boundary. `formals` is separate,
ordered user input; repetitions are meaningful relation argument positions.
Boundary wires not named by `formals` are the ambient parameter vector.
-/
structure ContentOccurrence
    (source : CheckedDiagram definitions)
    (pattern : CheckedOpenDiagram definitions) where
  selection : CheckedSelection source
  occurrence : Occurrence pattern source
  formals : List source.val.WireId

namespace ContentOccurrence

def parameters
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) :
    List source.val.WireId :=
  content.occurrence.boundaryAttachments.filter fun wire =>
    decide (wire ∉ content.formals)

def formalSigs
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) :
    List Sig :=
  content.formals.map fun wire => (source.val.wires wire).sig

def formalBoundaryPositions?
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) :
    Option (List Nat) :=
  content.formals.mapM fun wire =>
    (Data.Finite.indexOf?
      content.occurrence.boundaryAttachments wire).map Fin.val

def toConcreteSite
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) :
    ConcreteWireQuantifier.RelationSeverSite source where
  region := content.selection.region
  removedRegions := content.selection.allRegions
  removedNodes := content.selection.allNodes
  removedWires := content.selection.internalWires
  formals := content.formals

end ContentOccurrence

/-- Durable sever input; no occurrence is searched or inferred. -/
inductive WireSeverInput (source : CheckedDiagram definitions)
  | iota
      (orientation : Orientation)
      (wire : source.val.WireId)
      (keep : List (CEndpoint source.val.nodeCount))
  | relation
      (orientation : Orientation)
      (scope : source.val.RegionId)
      (pattern : CheckedOpenDiagram definitions)
      (occurrences : List (ContentOccurrence source pattern))

/-- Durable join input; relation content and parameter order are explicit. -/
inductive WireJoinInput (source : CheckedDiagram definitions)
  | iota
      (orientation : Orientation)
      (left right : source.val.WireId)
  | relation
      (orientation : Orientation)
      (wire : source.val.WireId)
      (content : CheckedOpenDiagram definitions)
      (parameters : List source.val.WireId)

private def severPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 0)
  | .backward => decide (depth % 2 = 1)

private def joinPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 1)
  | .backward => decide (depth % 2 = 0)

private structure CheckedSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  compiledAccepted : compileSite? source scope = some compiled
  legal :
    severPolarityLegal orientation compiled.frame.context.cutDepth = true

private structure CheckedJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  compiledAccepted : compileSite? source scope = some compiled
  legal :
    joinPolarityLegal orientation compiled.frame.context.cutDepth = true

private def endpointMember
    (endpoint : CEndpoint nodeCount)
    (endpoints : List (CEndpoint nodeCount)) : Bool :=
  decide (endpoint ∈ endpoints)

private def listsIntersect [DecidableEq α]
    (left right : List α) : Bool :=
  left.any fun value => decide (value ∈ right)

private def occurrenceOverlaps
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (left right : ContentOccurrence source pattern) : Bool :=
  decide (left.selection.region ∈ right.selection.allRegions) ||
    decide (right.selection.region ∈ left.selection.allRegions) ||
    listsIntersect left.selection.allRegions right.selection.allRegions ||
    listsIntersect left.selection.allNodes right.selection.allNodes ||
    listsIntersect left.selection.internalWires right.selection.internalWires ||
    decide
      (left.selection.region = right.selection.region ∧
        left.selection.allRegions.isEmpty ∧
        left.selection.allNodes.isEmpty ∧
        left.selection.internalWires.isEmpty ∧
        right.selection.allRegions.isEmpty ∧
        right.selection.allNodes.isEmpty ∧
        right.selection.internalWires.isEmpty)

private def pairwiseDisjoint
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions} :
    List (ContentOccurrence source pattern) → Bool
  | [] => true
  | head :: tail =>
      tail.all (fun candidate => !occurrenceOverlaps head candidate) &&
        pairwiseDisjoint tail

/--
Checker-owned evidence for one member of a nonempty relation-sever family.
The exact boundary order and scope containment are retained with the accepted
extraction; every member uses the head occurrence's ambient parameters.
-/
private structure CheckedOccurrence
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (first content : ContentOccurrence source pattern) : Type where
  extraction :
    CheckedExtraction content.selection content.occurrence
  boundaryExact :
    content.occurrence.boundaryAttachments =
      content.formals ++ content.parameters
  contained :
    source.val.Encloses scope content.selection.region
  parametersExact :
    content.parameters = first.parameters

/-- Pointwise checked evidence for the complete durable occurrence list. -/
private inductive CheckedOccurrenceList
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (first : ContentOccurrence source pattern) :
    List (ContentOccurrence source pattern) → Type
  | nil : CheckedOccurrenceList scope first []
  | cons
      {content : ContentOccurrence source pattern}
      {rest : List (ContentOccurrence source pattern)}
      (checked : CheckedOccurrence scope first content)
      (tail : CheckedOccurrenceList scope first rest) :
      CheckedOccurrenceList scope first (content :: rest)

/--
The sole retained validation receipt for one nonempty relation-sever family.
Its head owns the coherent ambient parameter vector and parameter-scope proof.
-/
private structure CheckedOccurrences
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (contents : List (ContentOccurrence source pattern)) : Type where
  first : ContentOccurrence source pattern
  rest : List (ContentOccurrence source pattern)
  contentsExact : contents = first :: rest
  entries : CheckedOccurrenceList scope first contents
  disjoint : pairwiseDisjoint contents = true
  parameterScopes :
    ∀ position : Fin first.parameters.length,
      source.val.Encloses
        (source.val.wires (first.parameters.get position)).scope scope

private def CheckedOccurrenceList.semanticEvidence
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)} :
    CheckedOccurrenceList scope first contents →
      List
        (WireQuantifierSemantics.RelationSeverOccurrence source pattern)
  | .nil => []
  | .cons (content := content) checked tail =>
      { selection := content.selection
        occurrence := content.occurrence
        extraction := checked.extraction
        formals := content.formals } :: tail.semanticEvidence

private def CheckedOccurrences.semanticEvidence
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {contents : List (ContentOccurrence source pattern)}
    (checked : CheckedOccurrences scope contents) :
    List
      (WireQuantifierSemantics.RelationSeverOccurrence source pattern) :=
  checked.entries.semanticEvidence

private def formalBoundaryValid
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) : Bool :=
  content.formals.all fun wire =>
    decide (wire ∈ content.occurrence.boundaryAttachments)

private def parametersEnclose
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (parameters : List source.val.WireId) : Bool :=
  parameters.all fun wire =>
    decide (source.val.Encloses (source.val.wires wire).scope scope)

private theorem parametersEnclose_of_true
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (parameters : List source.val.WireId)
    (accepted : parametersEnclose source scope parameters = true) :
    ∀ position : Fin parameters.length,
      source.val.Encloses
        (source.val.wires (parameters.get position)).scope scope := by
  intro position
  have member :
      parameters.get position ∈ parameters :=
    List.get_mem parameters position
  have checked :
      source.val.Encloses
        (source.val.wires (parameters.get position)).scope scope := by
    exact
      List.all_eq_true.mp (by
        simpa [parametersEnclose] using accepted)
        (parameters.get position) member
  exact checked

private def boundarySigs
    (content : CheckedOpenDiagram definitions) : List Sig :=
  content.val.boundary.map fun wire =>
    (content.val.diagram.wires wire).sig

private def splitAt? (count : Nat) (values : List α) :
    Option (List α × List α) :=
  if count ≤ values.length then
    some (values.take count, values.drop count)
  else
    none

private structure RelationApplication
    (source : CheckedDiagram definitions)
    (args : List Sig) where
  node : source.val.NodeId
  region : source.val.RegionId
  arguments : List source.val.WireId

private def argumentWires?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    List Sig → Nat → Option (List source.val.WireId)
  | [], _ => some []
  | expected :: rest, index => do
      let wire ← source.val.endpointOwner? ⟨node, .arg index⟩
      if (source.val.wires wire).sig = expected then
        let tail ← argumentWires? source node rest (index + 1)
        pure (wire :: tail)
      else
        none

private def applicationAt?
    (source : CheckedDiagram definitions)
    (relation : source.val.WireId)
    (args : List Sig)
    (endpoint : CEndpoint source.val.nodeCount) :
    Option (RelationApplication source args) := do
  if endpoint.port = .head then pure () else none
  match source.val.nodes endpoint.node with
  | .atom region nodeArgs =>
      if nodeArgs = args then
        if source.val.Encloses (source.val.wires relation).scope region then
          let arguments ← argumentWires? source endpoint.node args 0
          pure { node := endpoint.node, region := region, arguments := arguments }
        else
          none
      else
        none
  | _ => none

private def collectApplications?
    (source : CheckedDiagram definitions)
    (relation : source.val.WireId)
    (args : List Sig) :
    Option (List (RelationApplication source args)) := do
  let applications ←
    (source.val.wires relation).endpoints.mapM
      (applicationAt? source relation args)
  if applications.map (·.node) |>.Nodup then
    pure applications
  else
    none

private structure IotaJoinReceipt
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (left right : source.val.WireId)
    (target : CheckedDiagram definitions) where
  outer : source.val.WireId
  inner : source.val.WireId
  side :
    outer = left ∧ inner = right ∨
      outer = right ∧ inner = left
  comparable :
    source.val.Encloses
      (source.val.wires outer).scope
      (source.val.wires inner).scope
  polarity :
    CheckedJoinPolarity source orientation
      (source.val.wires inner).scope
  result : ConcreteWireQuantifier.IotaJoinResult source outer inner
  accepted :
    ConcreteWireQuantifier.joinIota source outer inner = .ok result
  targetExact : target = result.checked

private structure CheckedOpenCompilation
    (content : CheckedOpenDiagram definitions) where
  compilation : OpenCompilation content
  accepted : compileOpen content = some compilation

private structure CheckedRelationJoin
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) where
  polarity :
    CheckedJoinPolarity source orientation
      (source.val.wires wire).scope
  applications : List source.val.NodeId
  contentCompilation : CheckedOpenCompilation content
  parameterScopes :
    ∀ position : Fin parameters.length,
      source.val.Encloses
        (source.val.wires (parameters.get position)).scope
        (source.val.wires wire).scope

private structure RelationJoinReceipt
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (target : CheckedDiagram definitions)
    (applications : List source.val.NodeId) where
  polarity :
    CheckedJoinPolarity source orientation
      (source.val.wires wire).scope
  contentCompilation : CheckedOpenCompilation content
  result :
    ConcreteWireQuantifier.RelationJoinResult source wire content parameters
  accepted :
    ConcreteWireQuantifier.joinRelation source wire content parameters =
      .ok result
  targetExact : target = result.checked
  applicationsExact : applications = result.applications
  parameterScopes :
    ∀ position : Fin parameters.length,
      source.val.Encloses
        (source.val.wires (parameters.get position)).scope
        (source.val.wires wire).scope

private structure RelationSeverConcreteReceipt
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (occurrences : List (ContentOccurrence source pattern))
    (target : CheckedDiagram definitions) where
  extractions : CheckedOccurrences scope occurrences
  result :
    ConcreteWireQuantifier.RelationSeverResult source scope
      (extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site)
  accepted :
    ConcreteWireQuantifier.severRelation source scope
        (extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site) =
      .ok result
  targetExact : target = result.checked

private structure IotaSeverConcreteReceipt
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (target : CheckedDiagram definitions) where
  result : ConcreteWireQuantifier.IotaSeverResult source wire keep
  accepted :
    ConcreteWireQuantifier.severIota source wire keep = .ok result
  targetExact : target = result.checked

/-- Opaque accepted sever transformation. -/
structure AppliedWireSever
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) where
  private mk ::
  target : CheckedDiagram definitions
  private polarity :
    match input with
    | .iota orientation wire _ =>
        CheckedSeverPolarity source orientation
          (source.val.wires wire).scope
    | .relation orientation scope _ _ =>
        CheckedSeverPolarity source orientation scope
  private concrete :
    match input with
    | .iota _ wire keep =>
        IotaSeverConcreteReceipt source wire keep target
    | .relation _ scope _ occurrences =>
        RelationSeverConcreteReceipt source scope occurrences target

/-- Opaque accepted join transformation. -/
structure AppliedWireJoin
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) where
  private mk ::
  target : CheckedDiagram definitions
  applications : List source.val.NodeId
  private checked :
    match input with
    | .iota orientation left right =>
        IotaJoinReceipt source orientation left right target
    | .relation orientation wire content parameters =>
        RelationJoinReceipt source orientation wire content parameters
          target applications

private def requireSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except WireQuantifierError
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
    Except WireQuantifierError
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
    Except WireQuantifierError
      (CheckedOccurrence scope first content) := by
  match checkExtraction content.selection content.occurrence with
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
      Except WireQuantifierError
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
    Except WireQuantifierError
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
    Except WireQuantifierError
      (CheckedRelationJoin source orientation wire content parameters) := do
  let relation := source.val.wires wire
  let args ←
    match relation.sig with
    | .iota => throw .expectedRelation
    | .rel args => pure args
  let polarity ← requireJoinPolarity source orientation relation.scope
  let contentCompilation ←
    match accepted : compileOpen content with
    | none => throw .contentCompilationFailed
    | some compilation =>
        pure
          { compilation := compilation
            accepted := accepted }
  if wire ∈ parameters then
    throw .dyingWireIsParameter
  let contentSigs := boundarySigs content
  let split ←
    match splitAt? args.length contentSigs with
    | none => throw .boundaryTooShort
    | some split => pure split
  if split.1 != args then
    throw .boundarySignatureMismatch
  if split.2.length != parameters.length then
    throw .parameterMismatch
  if !(parameters.zip split.2).all
      (fun pair => (source.val.wires pair.1).sig == pair.2) then
    throw .parameterMismatch
  if accepted :
      parametersEnclose source relation.scope parameters = true then
    let applications ←
      match collectApplications? source wire args with
      | none => throw .nonAppliedEndpoint
      | some applications => pure applications
    pure
      { polarity := polarity
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
def applyWireSever
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) :
    Except WireQuantifierError (AppliedWireSever source input) := by
  cases input with
  | iota orientation wire keep =>
      let data := source.val.wires wire
      if data.sig != .iota then
        exact .error .expectedIota
      else if !keep.Nodup then
        exact .error .duplicateEndpoint
      else if !keep.all (fun endpoint => endpointMember endpoint data.endpoints) then
        exact .error .endpointNotOnWire
      else
        match requireSeverPolarity source orientation data.scope with
        | .error error => exact .error error
        | .ok polarity =>
            match accepted :
                ConcreteWireQuantifier.severIota source wire keep with
            | .error error => exact .error (.concreteRejected error)
            | .ok result =>
                exact .ok
                  (AppliedWireSever.mk result.checked polarity
                    { result := result
                      accepted := accepted
                      targetExact := rfl })
  | relation orientation scope pattern occurrences =>
      match validateRelationSever orientation scope pattern occurrences with
      | .error error => exact .error error
      | .ok validated =>
          let polarity := validated.1
          let extractions := validated.2
          let sites :=
            extractions.semanticEvidence.map
              WireQuantifierSemantics.RelationSeverOccurrence.site
          match accepted :
              ConcreteWireQuantifier.severRelation source scope sites with
          | .error error => exact .error (.concreteRejected error)
          | .ok result =>
                exact .ok
                  (AppliedWireSever.mk
                  result.checked polarity
                  { extractions := extractions
                    result := result
                    accepted := accepted
                    targetExact := rfl })

/--
Validate and apply one strongest join.  Relation joining consumes every
endpoint; no subset of applications is accepted.
-/
def applyWireJoin
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) :
    Except WireQuantifierError (AppliedWireJoin source input) := by
  cases input with
  | iota orientation left right =>
      if left = right then
        exact .error .incomparableScopes
      else if (source.val.wires left).sig != .iota ||
          (source.val.wires right).sig != .iota then
        exact .error .expectedIota
      else if leftOuter :
          source.val.Encloses (source.val.wires left).scope
            (source.val.wires right).scope then
        match requireJoinPolarity source orientation
            (source.val.wires right).scope with
        | .error error => exact .error error
        | .ok polarity =>
            match accepted :
                ConcreteWireQuantifier.joinIota source left right with
            | .error error => exact .error (.concreteRejected error)
            | .ok result =>
                exact .ok
                  (AppliedWireJoin.mk result.checked []
                    { outer := left
                      inner := right
                      side := Or.inl ⟨rfl, rfl⟩
                      comparable := leftOuter
                      polarity := polarity
                      result := result
                      accepted := accepted
                      targetExact := rfl })
      else if rightOuter :
          source.val.Encloses (source.val.wires right).scope
            (source.val.wires left).scope then
        match requireJoinPolarity source orientation
            (source.val.wires left).scope with
        | .error error => exact .error error
        | .ok polarity =>
            match accepted :
                ConcreteWireQuantifier.joinIota source right left with
            | .error error => exact .error (.concreteRejected error)
            | .ok result =>
                exact .ok
                  (AppliedWireJoin.mk result.checked []
                    { outer := right
                      inner := left
                      side := Or.inr ⟨rfl, rfl⟩
                      comparable := rightOuter
                      polarity := polarity
                      result := result
                      accepted := accepted
                      targetExact := rfl })
      else
        exact .error .incomparableScopes
  | relation orientation wire content parameters =>
      match validateRelationJoin orientation wire content parameters with
      | .error error => exact .error error
      | .ok validated =>
          match accepted :
              ConcreteWireQuantifier.joinRelation source wire content
              parameters with
          | .error error => exact .error (.concreteRejected error)
          | .ok result =>
              exact .ok
                (AppliedWireJoin.mk
                  result.checked result.applications
                  { polarity := validated.polarity
                    contentCompilation := validated.contentCompilation
                    result := result
                    accepted := accepted
                    targetExact := rfl
                    applicationsExact := rfl
                    parameterScopes := validated.parameterScopes })

/--
Individual abstraction is sound in the direction selected by the
checker-owned polarity receipt.
-/
theorem iota_sever_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (applied :
      AppliedWireSever source (.iota orientation wire keep))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed orientation
      (denoteChecked pre definitionEnv source)
      (denoteChecked pre definitionEnv applied.target) := by
  let checked := applied.concrete
  have sound :=
    checked.result.denotes applied.polarity.compiled pre definitionEnv
  rw [checked.targetExact]
  cases orientation with
  | forward =>
      have even :
          applied.polarity.compiled.frame.context.cutDepth % 2 = 0 :=
        of_decide_eq_true (by
          simpa [severPolarityLegal] using applied.polarity.legal)
      exact sound.1 even
  | backward =>
      have odd :
          applied.polarity.compiled.frame.context.cutDepth % 2 = 1 :=
        of_decide_eq_true (by
          simpa [severPolarityLegal] using applied.polarity.legal)
      exact sound.2 odd

/--
Comparable-scope individual grounding is sound in the direction selected by
the checker-owned polarity receipt.
-/
theorem iota_join_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (left right : source.val.WireId)
    (applied :
      AppliedWireJoin source (.iota orientation left right))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed orientation
      (denoteChecked pre definitionEnv source)
      (denoteChecked pre definitionEnv applied.target) := by
  let checked := applied.checked
  have sound :=
    checked.result.denotes checked.comparable checked.polarity.compiled
      pre definitionEnv
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
      AppliedWireJoin source
        (.relation orientation wire content parameters))
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

end WireQuantifier

export WireQuantifier
  (ContentOccurrence WireSeverInput WireJoinInput WireQuantifierError
    AppliedWireSever AppliedWireJoin applyWireSever applyWireJoin
    iota_sever_sound iota_join_sound relation_join_sound)

end VisualProof
