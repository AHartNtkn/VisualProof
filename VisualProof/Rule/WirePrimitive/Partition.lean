import VisualProof.Diagram.Concrete.WirePartitionIsomorphism
import VisualProof.Diagram.Concrete.WirePartitionSemantics
import VisualProof.Rule.Orientation

namespace VisualProof

namespace WirePrimitive

namespace Partition

/-- Stable refusal outcomes of generic signature-indexed partition/merge. -/
inductive WirePartitionError
  | duplicateEndpoint
  | endpointNotOnWire
  | severScopeOutsideWire
  | movedEndpointOutsideScope
  | signatureMismatch
  | incomparableScopes
  | severRequiresPositive
  | severBackwardRequiresNegative
  | joinRequiresNegative
  | joinBackwardRequiresPositive
  | scopeCompilationFailed
  | transportMismatch
  | concreteRejected (error : ConcreteWireQuantifier.Error)
  deriving Repr, DecidableEq

/-- Partition one wire, placing the moved endpoints on a wire at `scope`. -/
structure WireSeverInput (source : CheckedDiagram definitions) where
  orientation : Orientation
  wire : source.val.WireId
  keep : List (CEndpoint source.val.nodeCount)
  scope : source.val.RegionId

/-- Merge two distinct equal-signature wires at their outer scope. -/
structure WireJoinInput (source : CheckedDiagram definitions) where
  orientation : Orientation
  left : source.val.WireId
  right : source.val.WireId

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
  legal :
    severPolarityLegal orientation compiled.frame.context.cutDepth = true

private structure CheckedJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  legal :
    joinPolarityLegal orientation compiled.frame.context.cutDepth = true

private structure WireSeverReceipt
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) where
  polarity : CheckedSeverPolarity source input.orientation input.scope
  result :
    ConcreteWireQuantifier.WireSeverResult
      source input.wire input.keep input.scope
  accepted :
    ConcreteWireQuantifier.severWire
      source input.wire input.keep input.scope = .ok result

private structure WireJoinReceipt
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) where
  outer : source.val.WireId
  inner : source.val.WireId
  side :
    outer = input.left ∧ inner = input.right ∨
      outer = input.right ∧ inner = input.left
  comparable :
    source.val.Encloses
      (source.val.wires outer).scope
      (source.val.wires inner).scope
  polarity :
    CheckedJoinPolarity source input.orientation
      (source.val.wires inner).scope
  result : ConcreteWireQuantifier.WireJoinResult source outer inner
  accepted :
    ConcreteWireQuantifier.joinWires source outer inner = .ok result

/-- Opaque checker-owned receipt for one accepted wire partition. -/
structure AppliedWireSever
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) where
  private mk ::
  private checked : WireSeverReceipt source input

/-- Opaque checker-owned receipt for one accepted wire merge. -/
structure AppliedWireJoin
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) where
  private mk ::
  private checked : WireJoinReceipt source input

namespace AppliedWireSever

/-- The raw target is owned uniquely by the accepted concrete sever result. -/
def target
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (applied : AppliedWireSever source input) : CheckedDiagram definitions :=
  applied.checked.result.checked

end AppliedWireSever

namespace AppliedWireJoin

/-- The raw target is owned uniquely by the accepted concrete join result. -/
def target
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input) : CheckedDiagram definitions :=
  applied.checked.result.checked

end AppliedWireJoin

private def requireSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except WirePartitionError
      (CheckedSeverPolarity source orientation scope) := by
  match compileSite? source scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          severPolarityLegal orientation compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .severRequiresPositive
          | .backward => .severBackwardRequiresNegative

private def requireJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except WirePartitionError
      (CheckedJoinPolarity source orientation scope) := by
  match compileSite? source scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          joinPolarityLegal orientation compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .joinRequiresNegative
          | .backward => .joinBackwardRequiresPositive

private def endpointMember
    (endpoint : CEndpoint nodeCount)
    (endpoints : List (CEndpoint nodeCount)) : Bool :=
  decide (endpoint ∈ endpoints)

private def movedEndpointsEnclosed
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (scope : source.val.RegionId) : Bool :=
  (source.val.wires wire).endpoints.all fun endpoint =>
    decide (endpoint ∈ keep) ||
      decide
        (source.val.Encloses scope
          (source.val.nodes endpoint.node).region)

/-- Validate and apply one signature-indexed endpoint partition. -/
def applyWireSever
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) :
    Except WirePartitionError (AppliedWireSever source input) := by
  let data := source.val.wires input.wire
  if !input.keep.Nodup then
    exact .error .duplicateEndpoint
  else if !(input.keep.all
      (fun endpoint => endpointMember endpoint data.endpoints)) then
    exact .error .endpointNotOnWire
  else if !source.val.Encloses data.scope input.scope then
    exact .error .severScopeOutsideWire
  else if !(movedEndpointsEnclosed
      source input.wire input.keep input.scope) then
    exact .error .movedEndpointOutsideScope
  else
    match requireSeverPolarity source input.orientation input.scope with
    | .error error => exact .error error
    | .ok polarity =>
        match accepted :
            ConcreteWireQuantifier.severWire
              source input.wire input.keep input.scope with
        | .error error => exact .error (.concreteRejected error)
        | .ok result =>
            exact .ok
              (AppliedWireSever.mk
                { polarity := polarity
                  result := result
                  accepted := accepted })

/-- Validate and apply one equal-signature comparable-scope wire merge. -/
def applyWireJoin
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) :
    Except WirePartitionError (AppliedWireJoin source input) := by
  if input.left = input.right then
    exact .error .incomparableScopes
  else if (source.val.wires input.left).sig !=
      (source.val.wires input.right).sig then
    exact .error .signatureMismatch
  else if leftOuter :
      source.val.Encloses (source.val.wires input.left).scope
        (source.val.wires input.right).scope then
    match requireJoinPolarity source input.orientation
        (source.val.wires input.right).scope with
    | .error error => exact .error error
    | .ok polarity =>
        match accepted :
            ConcreteWireQuantifier.joinWires
              source input.left input.right with
        | .error error => exact .error (.concreteRejected error)
        | .ok result =>
            exact .ok
              (AppliedWireJoin.mk
                { outer := input.left
                  inner := input.right
                  side := Or.inl ⟨rfl, rfl⟩
                  comparable := leftOuter
                  polarity := polarity
                  result := result
                  accepted := accepted })
  else if rightOuter :
      source.val.Encloses (source.val.wires input.right).scope
        (source.val.wires input.left).scope then
    match requireJoinPolarity source input.orientation
        (source.val.wires input.left).scope with
    | .error error => exact .error error
    | .ok polarity =>
        match accepted :
            ConcreteWireQuantifier.joinWires
              source input.right input.left with
        | .error error => exact .error (.concreteRejected error)
        | .ok result =>
            exact .ok
              (AppliedWireJoin.mk
                { outer := input.right
                  inner := input.left
                  side := Or.inr ⟨rfl, rfl⟩
                  comparable := rightOuter
                  polarity := polarity
                  result := result
                  accepted := accepted })
  else
    exact .error .incomparableScopes

namespace AppliedWireSever

/-- Exact raw target image of one source wire through an accepted sever.  The
fresh split branch has no source preimage; every preexisting source wire uses
the stable carrier retained by the checker-owned sever result. -/
def rawWireImage
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (applied : AppliedWireSever source input)
    (wire : source.val.WireId) : applied.target.val.WireId :=
  applied.checked.result.wireImage wire

/-- Stable sever images never identify distinct source wires. -/
theorem rawWireImage_injective
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (applied : AppliedWireSever source input) :
    Function.Injective applied.rawWireImage := by
  obtain ⟨checked⟩ := applied
  intro left right same
  have imagesExact : checked.result.wireImage left =
      checked.result.wireImage right := by
    simpa [rawWireImage] using same
  let sourceOf : checked.result.checked.val.WireId → source.val.WireId :=
    fun mapped =>
      if fresh : mapped = checked.result.freshWire then
        input.wire
      else
        checked.result.sourceWireOfRetained mapped fresh
  have sourcesExact := congrArg sourceOf imagesExact
  simpa [sourceOf, checked.result.retained_ne_fresh] using sourcesExact

/-- Every severed source wire retains its exact signature at its raw image. -/
theorem rawWireImage_signature
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (applied : AppliedWireSever source input)
    (wire : source.val.WireId) :
    (applied.target.val.wires (applied.rawWireImage wire)).sig =
      (source.val.wires wire).sig := by
  obtain ⟨checked⟩ := applied
  exact checked.result.wireImage_signature wire

end AppliedWireSever

namespace AppliedWireJoin

/-- Logical raw image of an accepted join.  The checker-selected inner source
coalesces at the checked outer target; every retained source follows the
result's stable wire image. -/
def rawLogicalImage?
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input)
    (wire : source.val.WireId) : Option applied.target.val.WireId :=
  if same : wire = applied.checked.inner then
    some applied.checked.result.outerWire
  else
    some (applied.checked.result.wireImage wire same)

/-- External identity image of an accepted join.  The checker-selected inner
identity is consumed; every other source identity, including the stable outer
one, follows the retained result image. -/
def rawExternalImage?
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input)
    (wire : source.val.WireId) : Option applied.target.val.WireId :=
  if same : wire = applied.checked.inner then
    none
  else
    some (applied.checked.result.wireImage wire same)

/-- The logical join image is total, even for the coalesced inner source. -/
theorem rawLogicalImage_total
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input)
    (wire : source.val.WireId) :
    ∃ mapped, applied.rawLogicalImage? wire = some mapped := by
  obtain ⟨checked⟩ := applied
  by_cases same : wire = checked.inner
  · exact ⟨checked.result.outerWire, by
      simp [rawLogicalImage?, same]⟩
  · exact ⟨checked.result.wireImage wire same, by
      simp [rawLogicalImage?, same]⟩

/-- Every externally retained identity has exactly the same logical image. -/
theorem rawLogicalImage_of_rawExternalImage
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input)
    {wire : source.val.WireId}
    {mapped : applied.target.val.WireId}
    (mappedExact : applied.rawExternalImage? wire = some mapped) :
    applied.rawLogicalImage? wire = some mapped := by
  obtain ⟨checked⟩ := applied
  by_cases same : wire = checked.inner
  · simp [rawExternalImage?, same] at mappedExact
  · simpa [rawExternalImage?, rawLogicalImage?, same] using mappedExact

/-- An externally consumed source is exactly the coalesced side: its logical
image is shared with one distinct externally retained source.  This exposes
the mapped/unmapped consequence needed by transport consumers without
revealing which input wire the checker selected as inner or outer. -/
theorem rawExternalImage_none_coalesces
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input)
    {wire : source.val.WireId}
    (unmapped : applied.rawExternalImage? wire = none) :
    ∃ survivor mapped,
      survivor ≠ wire ∧
      applied.rawExternalImage? survivor = some mapped ∧
      applied.rawLogicalImage? wire = some mapped ∧
      applied.rawLogicalImage? survivor = some mapped := by
  obtain ⟨checked⟩ := applied
  by_cases same : wire = checked.inner
  · subst wire
    refine ⟨checked.outer, checked.result.outerWire,
      checked.result.outer_ne_inner, ?_⟩
    simp [rawExternalImage?, rawLogicalImage?,
      checked.result.outer_ne_inner,
      ConcreteWireQuantifier.WireJoinResult.outerWire]
  · simp [rawExternalImage?, same] at unmapped

/-- Logical coalescing preserves the source signature on both the selected
inner source and every retained source. -/
theorem rawLogicalImage_signature
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input)
    {wire : source.val.WireId}
    {mapped : applied.target.val.WireId}
    (mappedExact : applied.rawLogicalImage? wire = some mapped) :
    (applied.target.val.wires mapped).sig =
      (source.val.wires wire).sig := by
  obtain ⟨checked⟩ := applied
  by_cases same : wire = checked.inner
  · subst wire
    have targetExact : checked.result.outerWire = mapped := by
      simpa [rawLogicalImage?] using mappedExact
    subst mapped
    exact (checked.result.wireImage_signature
      checked.outer checked.result.outer_ne_inner).trans
        checked.result.source_signatures_equal
  · have targetExact : checked.result.wireImage wire same = mapped := by
      simpa [rawLogicalImage?, same] using mappedExact
    subst mapped
    exact checked.result.wireImage_signature wire same

/-- Retained join identities never collide in the raw target. -/
theorem rawExternalImage_injective
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input)
    {left right : source.val.WireId}
    {mapped : applied.target.val.WireId}
    (leftMapped : applied.rawExternalImage? left = some mapped)
    (rightMapped : applied.rawExternalImage? right = some mapped) :
    left = right := by
  obtain ⟨checked⟩ := applied
  by_cases leftSurvives : left = checked.inner
  · simp [rawExternalImage?, leftSurvives] at leftMapped
  · by_cases rightSurvives : right = checked.inner
    · simp [rawExternalImage?, rightSurvives] at rightMapped
    · have imagesExact :
        checked.result.wireImage left leftSurvives =
          checked.result.wireImage right rightSurvives := by
        have mappedSome :
            some (checked.result.wireImage left leftSurvives) =
              some (checked.result.wireImage right rightSurvives) := by
          simpa [rawExternalImage?, leftSurvives, rightSurvives] using
            leftMapped.trans rightMapped.symm
        exact Option.some.inj mappedSome
      have sourcesExact := congrArg checked.result.sourceWire imagesExact
      simpa using sourcesExact

/-- Every externally retained join identity preserves its exact signature. -/
theorem rawExternalImage_signature
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (applied : AppliedWireJoin source input)
    {wire : source.val.WireId}
    {mapped : applied.target.val.WireId}
    (mappedExact : applied.rawExternalImage? wire = some mapped) :
    (applied.target.val.wires mapped).sig =
      (source.val.wires wire).sig := by
  obtain ⟨checked⟩ := applied
  by_cases survives : wire = checked.inner
  · simp [rawExternalImage?, survives] at mappedExact
  · have targetExact : checked.result.wireImage wire survives = mapped := by
      simpa [rawExternalImage?, survives] using mappedExact
    subst mapped
    exact checked.result.wireImage_signature wire survives

end AppliedWireJoin

/-- Deterministic checked inverse of one accepted sever, owned by the sever
receipt rather than rediscovered from the target graph. -/
structure WireSeverInverse
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (applied : AppliedWireSever source input)
    (orientation : Orientation) where
  input : WireJoinInput applied.checked.result.checked
  applied : AppliedWireJoin applied.checked.result.checked input
  targetIso : ConcreteIso applied.target.val source.val

/-- Build the canonical inverse join named by the sever construction.  The
only executable refusal left is the inverse orientation's polarity gate. -/
def invertWireSever
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (applied : AppliedWireSever source input)
    (orientation : Orientation) :
    Except WirePartitionError (WireSeverInverse applied orientation) := by
  let result := applied.checked.result
  let left := result.wireImage input.wire
  let right := result.freshWire
  let inverseInput : WireJoinInput result.checked :=
    { orientation := orientation
      left := left
      right := right }
  match polarityAccepted :
      requireJoinPolarity result.checked orientation
        (result.checked.val.wires right).scope with
  | .error error => exact .error error
  | .ok polarity =>
      have comparable :
          result.checked.val.Encloses
            (result.checked.val.wires left).scope
            (result.checked.val.wires right).scope := by
        dsimp [left, right, result]
        rw [result.wireImage_scope, result.freshWire_scope]
        exact result.encloses_regionImage result.sourceScope_encloses_scope
      match accepted :
          ConcreteWireQuantifier.joinWires result.checked left right with
      | .error error => exact .error (.concreteRejected error)
      | .ok inverseResult =>
          have targetExact :
              inverseResult.checked = result.inverseJoin.checked := by
            apply Subtype.ext
            exact inverseResult.checked_generated.trans
              result.inverseJoin.checked_generated.symm
          let inverseApplied :
              AppliedWireJoin result.checked inverseInput :=
            AppliedWireJoin.mk
              { outer := left
                inner := right
                side := Or.inl ⟨rfl, rfl⟩
                comparable := comparable
                polarity := polarity
                result := inverseResult
                accepted := accepted }
          exact .ok
            { input := inverseInput
              applied := inverseApplied
              targetIso := by
                change ConcreteIso inverseResult.checked.val source.val
                rw [targetExact]
                exact result.inverseIso.symm }

/-- Deterministic inverse of an accepted sever after a suffix has renamed its
checked target.  The supplied isomorphism transports the two canonical join
parameters; no wire pair or target isomorphism is searched for. -/
structure TransportedWireSeverInverse
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (sever : AppliedWireSever source input)
    (real : CheckedDiagram definitions)
    (targetIso : ConcreteIso real.val sever.target.val)
    (orientation : Orientation) where
  input : WireJoinInput real
  orientationExact : input.orientation = orientation
  applied : AppliedWireJoin real input
  targetIso : ConcreteIso applied.target.val source.val

/-- Construct the inverse join from the canonical sever receipt after pulling
its parameters through the supplied suffix isomorphism. -/
def invertWireSeverTransported
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (sever : AppliedWireSever source input)
    (real : CheckedDiagram definitions)
    (targetIso : ConcreteIso real.val sever.target.val)
    (orientation : Orientation) :
    Except WirePartitionError
      (TransportedWireSeverInverse sever real targetIso orientation) := by
  let canonical := sever.checked.result
  have realToCanonical : ConcreteIso real.val canonical.checked.val := targetIso
  let left := realToCanonical.wires.symm
    (canonical.wireImage input.wire)
  let right := realToCanonical.wires.symm canonical.freshWire
  let inverseInput : WireJoinInput real :=
    { orientation := orientation
      left := left
      right := right }
  match polarityAccepted :
      requireJoinPolarity real orientation
        (real.val.wires right).scope with
  | .error error => exact .error error
  | .ok polarity =>
      have different : left ≠ right := by
        intro same
        have mapped := congrArg realToCanonical.wires same
        have leftExact : realToCanonical.wires left =
            canonical.wireImage input.wire := by
          change realToCanonical.wires.toFun
            (realToCanonical.wires.invFun
              (canonical.wireImage input.wire)) = _
          exact realToCanonical.wires.right_inv _
        have rightExact : realToCanonical.wires right =
            canonical.freshWire := by
          change realToCanonical.wires.toFun
            (realToCanonical.wires.invFun canonical.freshWire) = _
          exact realToCanonical.wires.right_inv _
        rw [leftExact, rightExact] at mapped
        exact canonical.inverseJoin.outer_ne_inner mapped
      have signaturesEqual :
          (real.val.wires left).sig = (real.val.wires right).sig := by
        have leftSig := realToCanonical.wire_signature left
        have rightSig := realToCanonical.wire_signature right
        have leftExact : realToCanonical.wires left =
            canonical.wireImage input.wire := by
          change realToCanonical.wires.toFun
            (realToCanonical.wires.invFun
              (canonical.wireImage input.wire)) = _
          exact realToCanonical.wires.right_inv _
        have rightExact : realToCanonical.wires right =
            canonical.freshWire := by
          change realToCanonical.wires.toFun
            (realToCanonical.wires.invFun canonical.freshWire) = _
          exact realToCanonical.wires.right_inv _
        rw [leftExact] at leftSig
        rw [rightExact] at rightSig
        exact leftSig.symm.trans
          (canonical.inverseJoin.source_signatures_equal.trans rightSig)
      have comparable :
          real.val.Encloses
            (real.val.wires left).scope
            (real.val.wires right).scope := by
        have canonicalComparable :
            canonical.checked.val.Encloses
              (canonical.checked.val.wires
                (canonical.wireImage input.wire)).scope
              (canonical.checked.val.wires canonical.freshWire).scope := by
          rw [canonical.wireImage_scope, canonical.freshWire_scope]
          exact canonical.encloses_regionImage
            canonical.sourceScope_encloses_scope
        have pulled := realToCanonical.symm.encloses_transport
          canonicalComparable
        have leftScope :
            (real.val.wires left).scope =
              realToCanonical.regions.symm
                (canonical.checked.val.wires
                  (canonical.wireImage input.wire)).scope := by
          simpa [left] using
            realToCanonical.symm.wire_scope
              (canonical.wireImage input.wire)
        have rightScope :
            (real.val.wires right).scope =
              realToCanonical.regions.symm
                (canonical.checked.val.wires canonical.freshWire).scope := by
          simpa [right] using
            realToCanonical.symm.wire_scope canonical.freshWire
        rw [leftScope, rightScope]
        exact pulled
      match accepted : ConcreteWireQuantifier.joinWires real left right with
      | .error error => exact .error (.concreteRejected error)
      | .ok actual =>
          let inverseApplied : AppliedWireJoin real inverseInput :=
            AppliedWireJoin.mk
              { outer := left
                inner := right
                side := Or.inl ⟨rfl, rfl⟩
                comparable := comparable
                polarity := polarity
                result := actual
                accepted := accepted }
          match natural : actual.transportedIso? realToCanonical
              canonical.inverseJoin
              (by
                change realToCanonical.wires.toFun
                  (realToCanonical.wires.invFun
                    (canonical.wireImage input.wire)) = _
                exact realToCanonical.wires.right_inv _)
              (by
                change realToCanonical.wires.toFun
                  (realToCanonical.wires.invFun canonical.freshWire) = _
                exact realToCanonical.wires.right_inv _) with
          | none => exact .error .transportMismatch
          | some outputIso =>
              exact .ok
                { input := inverseInput
                  orientationExact := rfl
                  applied := inverseApplied
                  targetIso := outputIso.trans canonical.inverseIso.symm }

/-- Deterministic inverse of an accepted join after a suffix has renamed its
checked target. The join receipt owns the exact outer endpoint partition and
inner scope used by the inverse sever. -/
structure TransportedWireJoinInverse
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (join : AppliedWireJoin source input)
    (real : CheckedDiagram definitions)
    (targetIso : ConcreteIso real.val join.target.val)
    (orientation : Orientation) where
  input : WireSeverInput real
  orientationExact : input.orientation = orientation
  applied : AppliedWireSever real input
  targetIso : ConcreteIso applied.target.val source.val

/-- Pull the canonical inverse partition through the supplied suffix
isomorphism, invoke exactly one sever checker, and validate the explicitly
constructed output-to-source carrier equivalences. -/
def invertWireJoinTransported
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source}
    (join : AppliedWireJoin source input)
    (real : CheckedDiagram definitions)
    (targetIso : ConcreteIso real.val join.target.val)
    (orientation : Orientation) :
    Except WirePartitionError
      (TransportedWireJoinInverse join real targetIso orientation) := by
  let canonical := join.checked.result
  have realToCanonical : ConcreteIso real.val canonical.checked.val := targetIso
  let canonicalKeep :=
    (source.val.wires join.checked.outer).endpoints.map
      canonical.endpointImage
  have canonicalKeepMembers :
      ∀ endpoint, endpoint ∈ canonicalKeep →
        endpoint ∈
          (canonical.checked.val.wires canonical.outerWire).endpoints := by
    intro endpoint member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    change canonical.endpointImage original ∈
      (canonical.checked.val.wires
        (canonical.wireImage join.checked.outer
          canonical.outer_ne_inner)).endpoints
    rw [canonical.wireImage_endpoints join.checked.outer
      canonical.outer_ne_inner]
    rw [if_pos rfl]
    exact List.mem_map.mpr
      ⟨original, List.mem_append_left _ originalMember, rfl⟩
  let realWire := realToCanonical.wires.symm canonical.outerWire
  let realKeep := realToCanonical.symm.transportEndpointsOnWire
    canonical.outerWire canonicalKeep canonicalKeepMembers
  let canonicalScope := canonical.regionImage
    (source.val.wires join.checked.inner).scope
  let realScope := realToCanonical.regions.symm canonicalScope
  let inverseInput : WireSeverInput real :=
    { orientation := orientation
      wire := realWire
      keep := realKeep
      scope := realScope }
  match appliedResult : applyWireSever real inverseInput with
  | .error error => exact .error error
  | .ok inverseApplied =>
      let actual := inverseApplied.checked.result
      have regionCountExact :
          actual.checked.val.regionCount = source.val.regionCount :=
        actual.regionCount.trans
          (realToCanonical.regionCount_eq.trans canonical.regionCount)
      have nodeCountExact :
          actual.checked.val.nodeCount = source.val.nodeCount :=
        actual.nodeCount.trans
          (realToCanonical.nodeCount_eq.trans canonical.nodeCount)
      have wireCountExact :
          actual.checked.val.wireCount = source.val.wireCount := by
        calc
          actual.checked.val.wireCount = real.val.wireCount + 1 :=
            actual.wireCount
          _ = canonical.checked.val.wireCount + 1 :=
            congrArg (fun count => count + 1)
              realToCanonical.wireCount_eq
          _ = source.val.wireCount := canonical.wireCount_succ
      let regionEquiv : Data.Finite.FiniteEquiv
          actual.checked.val.RegionId source.val.RegionId :=
        { toFun := Fin.cast regionCountExact
          invFun := Fin.cast regionCountExact.symm
          left_inv := by intro region; apply Fin.ext; rfl
          right_inv := by intro region; apply Fin.ext; rfl }
      let nodeEquiv : Data.Finite.FiniteEquiv
          actual.checked.val.NodeId source.val.NodeId :=
        { toFun := Fin.cast nodeCountExact
          invFun := Fin.cast nodeCountExact.symm
          left_inv := by intro node; apply Fin.ext; rfl
          right_inv := by intro node; apply Fin.ext; rfl }
      let originalWire : actual.checked.val.WireId → source.val.WireId :=
        fun output =>
          if fresh : output = actual.freshWire then
            join.checked.inner
          else
            canonical.sourceWire
              (realToCanonical.wires
                (actual.sourceWireOfRetained output fresh))
      let inverseWire : source.val.WireId → actual.checked.val.WireId :=
        fun original =>
          if removed : original = join.checked.inner then
            actual.freshWire
          else
            actual.wireImage
              (realToCanonical.wires.symm
                (canonical.wireImage original removed))
      have inverseWire_left :
          ∀ original, originalWire (inverseWire original) = original := by
        intro original
        by_cases removed : original = join.checked.inner
        · subst original
          simp [originalWire, inverseWire]
        · have retained := actual.retained_ne_fresh
              (realToCanonical.wires.symm
                (canonical.wireImage original removed))
          dsimp [inverseWire, originalWire]
          rw [dif_neg removed]
          split
          · rename_i same
            exact False.elim (retained same)
          · rw [actual.sourceWireOfRetained_wireImage,
              realToCanonical.wires.right_inv,
              canonical.sourceWire_wireImage]
      have inverseWire_right :
          ∀ output, inverseWire (originalWire output) = output := by
        intro output
        by_cases fresh : output = actual.freshWire
        · subst output
          simp [originalWire, inverseWire]
        · let retained := actual.sourceWireOfRetained output fresh
          have sourceNotInner := canonical.sourceWire_ne_inner
            (realToCanonical.wires retained)
          dsimp [originalWire, inverseWire]
          rw [dif_neg fresh]
          rw [dif_neg sourceNotInner,
            canonical.wireImage_sourceWire,
            realToCanonical.wires.left_inv,
            actual.wireImage_sourceWireOfRetained]
      let wireEquiv : Data.Finite.FiniteEquiv
          actual.checked.val.WireId source.val.WireId :=
        { toFun := originalWire
          invFun := inverseWire
          left_inv := inverseWire_right
          right_inv := inverseWire_left }
      match checkedIso : ConcreteIso.checkEquivs? actual.checked.val
          source.val regionEquiv nodeEquiv wireEquiv with
      | none => exact .error .transportMismatch
      | some sourceIso =>
          exact .ok
            { input := inverseInput
              orientationExact := rfl
              applied := inverseApplied
              targetIso := sourceIso }

/-- Generic signature-indexed wire partition is sound over every premodel. -/
theorem wire_sever_sound
    {source : CheckedDiagram definitions}
    (input : WireSeverInput source)
    (applied : AppliedWireSever source input)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed input.orientation
      (denoteChecked pre definitionEnv source)
      (denoteChecked pre definitionEnv applied.target) := by
  rcases input with ⟨orientation, wire, keep, scope⟩
  let checked := applied.checked
  have sound :=
    checked.result.denotes checked.polarity.compiled pre definitionEnv
  cases orientation with
  | forward =>
      have even :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 0 :=
        of_decide_eq_true (by
          simpa [severPolarityLegal] using checked.polarity.legal)
      exact sound.1 even
  | backward =>
      have odd :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 1 :=
        of_decide_eq_true (by
          simpa [severPolarityLegal] using checked.polarity.legal)
      exact sound.2 odd

/-- Generic equal-signature wire merge is sound over every premodel. -/
theorem wire_join_sound
    {source : CheckedDiagram definitions}
    (input : WireJoinInput source)
    (applied : AppliedWireJoin source input)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed input.orientation
      (denoteChecked pre definitionEnv source)
      (denoteChecked pre definitionEnv applied.target) := by
  rcases input with ⟨orientation, left, right⟩
  let checked := applied.checked
  have sound :=
    checked.result.denotes checked.comparable checked.polarity.compiled
      pre definitionEnv
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

end Partition

export Partition
  (WireSeverInput WireJoinInput WirePartitionError
    AppliedWireSever AppliedWireJoin applyWireSever applyWireJoin
    wire_sever_sound wire_join_sound)

end WirePrimitive

export WirePrimitive
  (WireSeverInput WireJoinInput WirePartitionError
    AppliedWireSever AppliedWireJoin applyWireSever applyWireJoin
    wire_sever_sound wire_join_sound)

end VisualProof
