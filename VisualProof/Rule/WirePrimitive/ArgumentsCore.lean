import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveComplete
import VisualProof.Rule.Tag
import VisualProof.Rule.Orientation

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

/-- Stable public refusal outcomes for argument-plumbing primitives. -/
inductive WireArgumentError
  | dropRequiresNegative
  | dropBackwardRequiresPositive
  | extendRequiresPositive
  | extendBackwardRequiresNegative
  | scopeCompilationFailed
  | semanticLedgerRejected
  | concreteRejected (error : ConcreteWirePrimitive.ArgumentError)
  deriving Repr, DecidableEq

namespace Internal

def optionToExcept
    (error : WireArgumentError) : Option α → Except WireArgumentError α
  | none => .error error
  | some value => .ok value

def joinPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 1)
  | .backward => decide (depth % 2 = 0)

def severPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 0)
  | .backward => decide (depth % 2 = 1)

structure CheckedDropPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  compiled :
    SiteCompilation source (source.val.wires wire).scope
  legal :
    joinPolarityLegal orientation compiled.frame.context.cutDepth = true

structure CheckedExtendPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  compiled :
    SiteCompilation source (source.val.wires wire).scope
  legal :
    severPolarityLegal orientation compiled.frame.context.cutDepth = true

def requireDropPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) :
    Except WireArgumentError
      (CheckedDropPolarity source orientation wire) := by
  match compileSite? source (source.val.wires wire).scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          joinPolarityLegal orientation
            compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .dropRequiresNegative
          | .backward => .dropBackwardRequiresPositive

def requireExtendPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) :
    Except WireArgumentError
      (CheckedExtendPolarity source orientation wire) := by
  match compileSite? source (source.val.wires wire).scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          severPolarityLegal orientation
            compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .extendRequiresPositive
          | .backward => .extendBackwardRequiresNegative

/--
The merged checker exempts exactly one shared attachment visible at the acted
wire's scope.  Empty site families have no such attachment and use the
ordinary polarity gate.
-/
def uniformVisibleAttachment
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId) : Bool :=
  match attachments with
  | [] => false
  | first :: rest =>
      rest.all (· == first) &&
        decide
          (source.val.Encloses
            (source.val.wires first).scope
            (source.val.wires wire).scope)

inductive DropGate
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId)
  | uniform :
      uniformVisibleAttachment source wire attachments = true →
      DropGate source orientation wire attachments
  | gated :
      uniformVisibleAttachment source wire attachments = false →
      CheckedDropPolarity source orientation wire →
      DropGate source orientation wire attachments

inductive ExtendGate
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId)
  | uniform :
      uniformVisibleAttachment source wire attachments = true →
      ExtendGate source orientation wire attachments
  | gated :
      uniformVisibleAttachment source wire attachments = false →
      CheckedExtendPolarity source orientation wire →
      ExtendGate source orientation wire attachments

def checkDropGate
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId) :
    Except WireArgumentError
      (DropGate source orientation wire attachments) := by
  if uniform :
      uniformVisibleAttachment source wire attachments = true then
    exact .ok (.uniform uniform)
  else
    match requireDropPolarity source orientation wire with
    | .error error => exact .error error
    | .ok polarity =>
        have notUniform :
            uniformVisibleAttachment source wire attachments = false := by
          cases value :
              uniformVisibleAttachment source wire attachments <;>
            simp_all
        exact .ok
          (.gated notUniform polarity)

def checkExtendGate
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId) :
    Except WireArgumentError
      (ExtendGate source orientation wire attachments) := by
  if uniform :
      uniformVisibleAttachment source wire attachments = true then
    exact .ok (.uniform uniform)
  else
    match requireExtendPolarity source orientation wire with
    | .error error => exact .error error
    | .ok polarity =>
        have notUniform :
            uniformVisibleAttachment source wire attachments = false := by
          cases value :
              uniformVisibleAttachment source wire attachments <;>
            simp_all
        exact .ok
          (.gated notUniform polarity)

inductive DropSemanticReceipt
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger :
      ArgumentsSemantics.DropLedger result sourceArguments)
  | uniform
      (fixed : ArgumentsSemantics.FixedDropLedger ledger)
  | gated
      (polarity : CheckedDropPolarity source orientation wire)

inductive ExtendSemanticReceipt
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger :
      ArgumentsSemantics.ExtendLedger result sourceArguments)
  | uniform
      (fixed : ArgumentsSemantics.FixedExtendLedger ledger)
  | gated
      (polarity : CheckedExtendPolarity source orientation wire)


end Internal

structure AppliedArgDuplicate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private source_removed_exact : result.sourceRemovedWires = [wire]
  private local_count_exact : result.spec.localCount = 0
  private target_arguments_exact :
    result.targetArguments =
      ConcreteWirePrimitive.insertAt sourceArguments (position + 1)
        (sourceArguments[position]?.getD .iota)
  private arguments_exact :
    ∀ site : Fin result.sites.sites.length,
      result.spec.arguments site = existingReferences
        (ConcreteWirePrimitive.insertAt
          (result.sites.sites.get site).arguments (position + 1)
          ((result.sites.sites.get site).arguments[position]?.getD wire))
  private position_valid : position < sourceArguments.length
  private ledger :
    ArgumentsSemantics.DuplicateLedger result sourceArguments

structure AppliedArgContract
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private source_removed_exact : result.sourceRemovedWires = [wire]
  private local_count_exact : result.spec.localCount = 0
  private target_arguments_exact :
    result.targetArguments =
      ConcreteWirePrimitive.eraseAt sourceArguments (position + 1)
  private arguments_exact :
    ∀ site : Fin result.sites.sites.length,
      result.spec.arguments site = existingReferences
        (ConcreteWirePrimitive.eraseAt
          (result.sites.sites.get site).arguments (position + 1))
  private ledger :
    ArgumentsSemantics.ContractLedger result sourceArguments


namespace AppliedArgDuplicate

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgDuplicate source wire position) := source

/-- Checker-owned concrete construction receipt for transport proofs. -/
def argumentResult
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :=
  applied.result

/-- Argument duplication removes only its acted source head. -/
theorem sourceRemovedWires_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    applied.argumentResult.sourceRemovedWires = [wire] :=
  applied.source_removed_exact

/-- Argument duplication allocates no construction-local wires. -/
theorem localCount_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    applied.argumentResult.spec.localCount = 0 :=
  applied.local_count_exact

def sourceArgumentList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) : List Sig :=
  applied.sourceArguments

/-- Checker-owned source sites rebuilt by argument duplication. -/
def sourceSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    AllAppliedSites source wire :=
  applied.result.sites

def targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (site : Fin applied.sourceSites.sites.length) :
    applied.result.target.val.NodeId :=
  applied.result.targetNode site

theorem sourceWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    (source.val.wires wire).sig = .rel applied.sourceArgumentList :=
  applied.sourceSignature

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

/-- Checker-owned typed duplication witness used by cancellation transport. -/
def duplicationEvidence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    ArgumentsSemantics.TypedArguments.DuplicationEvidence
      applied.sourceArgumentList applied.argumentResult.targetArguments :=
  applied.ledger.retraction

/-- Checker-owned argument factorization used by cancellation transport. -/
def argumentFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :=
  applied.ledger.factorization

def nodeEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    Data.Finite.FiniteEquiv source.val.NodeId applied.target.val.NodeId :=
  applied.result.nodeEquiv applied.targetSites

def wireEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    Data.Finite.FiniteEquiv source.val.WireId applied.target.val.WireId :=
  applied.result.wireEquivHeadOnly applied.source_removed_exact
    applied.local_count_exact

@[simp] theorem wireEquiv_head
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    applied.wireEquiv wire = applied.targetWire := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly
  simp
  rfl

theorem nodeEquiv_generated
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (site : Fin applied.result.sites.sites.length) :
    applied.nodeEquiv (applied.result.sites.sites.get site).node =
      applied.result.targetNode site := by
  have generated : (applied.result.sites.sites.get site).node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨applied.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage
      (applied.result.sites.sites.get site).node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_pos generated]
  rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get
    applied.result.sites site generated]

theorem nodeEquiv_generated_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (node : source.val.NodeId)
    (generated : node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    applied.nodeEquiv node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.targetSites := by
  let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
    applied.sourceSites node generated
  have sourceExact : (applied.sourceSites.sites.get site).node = node :=
    ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
      applied.sourceSites node generated
  rw [← sourceExact]
  change applied.nodeEquiv (applied.result.sites.sites.get site).node ∈ _
  rw [applied.nodeEquiv_generated site]
  exact applied.result.generatedNode_targetSiteNode applied.targetSites site

theorem nodeEquiv_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (node : source.val.NodeId)
    (retained : node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites) :
    applied.nodeEquiv node =
      applied.result.retainedNodeImage node retained := by
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retained]

theorem wireEquiv_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.wireEquiv sourceWire =
      applied.result.retainedWireImage sourceWire (by
        rw [applied.source_removed_exact]
        simpa [different]) := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
  change (if same : sourceWire = wire then applied.result.targetWire
    else applied.result.retainedWireImage sourceWire _) = _
  rw [dif_neg different]

theorem wireEquiv_retained_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  rw [applied.wireEquiv_retained sourceWire different]
  exact applied.result.retainedWireImage_signature sourceWire _

theorem wireEquiv_retained_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).scope =
      applied.result.regionEquiv (source.val.wires sourceWire).scope := by
  rw [applied.wireEquiv_retained sourceWire different,
    show
      (applied.target.val.wires
          (applied.result.retainedWireImage sourceWire _)).scope =
        applied.result.regionImage (source.val.wires sourceWire).scope by
      exact applied.result.retainedWireImage_scope sourceWire _]
  exact applied.result.regionImage_exact _

theorem targetArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    applied.result.targetArguments =
      ConcreteWirePrimitive.insertAt applied.sourceArgumentList (position + 1)
        (applied.sourceArgumentList[position]?.getD .iota) :=
  applied.target_arguments_exact

theorem positionValid
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    position < applied.sourceArgumentList.length :=
  applied.position_valid

def targetArgumentList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) : List Sig :=
  applied.result.targetArguments

theorem targetWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    (applied.target.val.wires applied.targetWire).sig =
      .rel applied.targetArgumentList :=
  applied.argumentResult.targetWire_signature

/-- Every generated duplicate application uses the exact checker-owned attachment
vector at its source-site position. -/
theorem siteArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (site : Fin applied.result.sites.sites.length) :
    applied.result.spec.arguments site =
      existingReferences
        (ConcreteWirePrimitive.insertAt
          (applied.result.sites.sites.get site).arguments (position + 1)
          ((applied.result.sites.sites.get site).arguments[position]?.getD
            wire)) :=
  applied.arguments_exact site

/-- A generated drop argument endpoint is owned by the checked image of the
exact attachment selected at that output position. -/
theorem generatedArgument_endpointOwner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (site : Fin applied.result.sites.sites.length)
    (targetPosition : Nat)
    (targetBound : targetPosition < applied.result.targetArguments.length)
    (sourceWire : source.val.WireId)
    (selected : (applied.result.spec.arguments site)[targetPosition]? =
      some (.existing sourceWire)) :
    applied.target.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg targetPosition⟩ =
      some (applied.wireEquiv sourceWire) := by
  by_cases different : sourceWire ≠ wire
  · have retained : sourceWire ∉ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simpa [different]
    have owner := applied.result.generatedArgument_endpointOwner site
      targetPosition targetBound sourceWire selected retained
    simpa [AppliedArgDuplicate.wireEquiv,
      ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly,
      ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly, different]
      using owner
  · have same : sourceWire = wire := Classical.not_not.mp different
    subst sourceWire
    rw [applied.wireEquiv_head]
    change applied.result.checked.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg targetPosition⟩ =
      some applied.result.targetWire
    rw [applied.result.targetNode_argument_owner site targetPosition
      targetBound]
    congr 1
    unfold ConcreteWirePrimitive.replacementOwner
      ConcreteWirePrimitive.replacementNode
    simp only [Fin.addCases_right]
    rw [selected]
    simp only
    rw [ConcreteWirePrimitive.retainedReplacementWire?_head_none]
    exact applied.result.targetWire_exact.symm

/-- Public list-indexed form of generated duplicate endpoint ownership. -/
theorem generatedArgument_endpointOwner_of_selected
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (site : Fin applied.sourceSites.sites.length)
    (targetPosition : Nat)
    (targetBound : targetPosition < applied.targetArgumentList.length)
    (sourceWire : source.val.WireId)
    (selected :
      (ConcreteWirePrimitive.insertAt
        (applied.sourceSites.sites.get site).arguments (position + 1)
        ((applied.sourceSites.sites.get site).arguments[position]?.getD
          wire))[
          targetPosition]? = some sourceWire) :
    applied.target.val.endpointOwner?
        ⟨applied.targetNode site, .arg targetPosition⟩ =
      some (applied.wireEquiv sourceWire) := by
  apply applied.generatedArgument_endpointOwner site targetPosition
    targetBound sourceWire
  rw [applied.siteArguments_exact site]
  unfold existingReferences
  rw [List.getElem?_map, show
    (ConcreteWirePrimitive.insertAt
      (applied.result.sites.sites.get site).arguments (position + 1)
      ((applied.result.sites.sites.get site).arguments[position]?.getD wire))[
        targetPosition]? = some sourceWire by
      simpa [sourceSites] using selected]
  rfl

/-- Exact target image of any source wire through argument duplication.  The acted
head is replaced by the checked target head; every other wire is transported
by the replacement receipt's retained-wire map. -/
def transportWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (sourceWire : source.val.WireId) :
    applied.target.val.WireId :=
  if same : sourceWire = wire then
    applied.targetWire
  else
    applied.result.retainedWireImage sourceWire (by
      rw [applied.source_removed_exact]
      simpa [same])

theorem transportWire_eq_wireEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (sourceWire : source.val.WireId) :
    applied.transportWire sourceWire = applied.wireEquiv sourceWire := by
  unfold transportWire wireEquiv
    ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly
  rfl

/-- Pushing an endpoint of a retained node through argument duplication preserves
its port and incidence on the exact transported wire. -/
theorem retainedEndpointImage_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (sourceWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires sourceWire).endpoints)
    (retained : endpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    (⟨applied.nodeEquiv endpoint.node, endpoint.port⟩ :
      CEndpoint applied.target.val.nodeCount) ∈
      (applied.target.val.wires
        (applied.wireEquiv sourceWire)).endpoints := by
  have sourceWireDifferent : sourceWire ≠ wire := by
    intro same
    subst sourceWire
    have removed : wire ∈ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simp
    exact retained (applied.result.sourceRemovedExhausted wire removed
      endpoint incident)
  have sourceRetained : sourceWire ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [sourceWireDifferent]
  have targetIncident := applied.result.retainedNode_forwardIncident
    endpoint.node retained endpoint.port sourceWire incident
  have nodeImage := applied.nodeEquiv_retained endpoint.node retained
  have wireImage := applied.wireEquiv_retained sourceWire sourceWireDifferent
  have contextImage := applied.result.contextWireMap_retained sourceWire
    sourceRetained
  rw [contextImage, ← wireImage] at targetIncident
  simpa [nodeImage] using targetIncident

/-- Pulling an endpoint of a retained rebuilt node through argument duplication
preserves its port and recovers incidence on the exact source wire. -/
theorem retainedEndpointInverse_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position)
    (sourceWire : source.val.WireId)
    (candidate : CEndpoint applied.target.val.nodeCount)
    (incident : candidate ∈
      (applied.target.val.wires
        (applied.wireEquiv sourceWire)).endpoints)
    (retained : applied.nodeEquiv.symm candidate.node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    (⟨applied.nodeEquiv.symm candidate.node, candidate.port⟩ :
      CEndpoint source.val.nodeCount) ∈
      (source.val.wires sourceWire).endpoints := by
  let sourceNode := applied.nodeEquiv.symm candidate.node
  have nodeRecover : applied.nodeEquiv sourceNode = candidate.node :=
    applied.nodeEquiv.right_inv candidate.node
  have targetRequired : candidate.port ∈
      applied.target.val.requiredPorts candidate.node :=
    ConcreteDiagram.incident_port_required definitions applied.target.val
      applied.target.property (applied.wireEquiv sourceWire) candidate incident
  have targetNodeImage : applied.result.retainedNodeImage sourceNode retained =
      candidate.node := by
    rw [← applied.nodeEquiv_retained sourceNode retained]
    exact nodeRecover
  have sourceRequired : candidate.port ∈
      source.val.requiredPorts sourceNode := by
    have retainedData : applied.target.val.nodes
        (applied.result.retainedNodeImage sourceNode retained) =
          (source.val.nodes sourceNode).rename applied.result.regionEquiv :=
      applied.result.retainedNodeImage_data sourceNode retained
    rw [ConcreteDiagram.requiredPorts] at targetRequired ⊢
    rw [← targetNodeImage, retainedData] at targetRequired
    cases sourceData : source.val.nodes sourceNode <;>
      simp [sourceData, CNode.rename] at targetRequired ⊢
    all_goals exact targetRequired
  obtain ⟨actualWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions source.val
      source.property sourceNode candidate.port sourceRequired
  have actualDifferent : actualWire ≠ wire := by
    intro same
    subst actualWire
    have actualIncident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode, candidate.port⟩ wire sourceOwner
    have removed : wire ∈ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simp
    exact retained (applied.result.sourceRemovedExhausted wire removed
      ⟨sourceNode, candidate.port⟩ actualIncident)
  have actualRetained : actualWire ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [actualDifferent]
  have forwardOwner := applied.result.retainedNodeImage_endpointOwner
    sourceNode retained candidate.port sourceRequired actualWire sourceOwner
  change applied.target.val.endpointOwner?
      ⟨applied.result.retainedNodeImage sourceNode retained,
        candidate.port⟩ =
    some (applied.result.retainedWireImage actualWire actualRetained)
    at forwardOwner
  have targetOwner : applied.target.val.endpointOwner? candidate =
      some (applied.wireEquiv sourceWire) :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions
      applied.target.val applied.target.property candidate.node candidate.port
      targetRequired (applied.wireEquiv sourceWire) incident
  rw [targetNodeImage, targetOwner,
    ← applied.wireEquiv_retained actualWire actualDifferent]
    at forwardOwner
  have actualExact : actualWire = sourceWire :=
    applied.wireEquiv.injective (Option.some.inj forwardOwner).symm
  subst actualWire
  exact ConcreteDiagram.endpointOwner?_incident source.val
    ⟨sourceNode, candidate.port⟩ sourceWire sourceOwner

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgDuplicate source wire position) : StepTag :=
  .argDuplicate

end AppliedArgDuplicate
namespace AppliedArgContract

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgContract source wire position) := source

/-- Checker-owned concrete construction receipt for transport proofs. -/
def argumentResult
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :=
  applied.result

/-- Argument contraction removes only its acted source head. -/
theorem sourceRemovedWires_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    applied.argumentResult.sourceRemovedWires = [wire] :=
  applied.source_removed_exact

/-- Argument contraction allocates no construction-local wires. -/
theorem localCount_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    applied.argumentResult.spec.localCount = 0 :=
  applied.local_count_exact

def sourceArgumentList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) : List Sig :=
  applied.sourceArguments

/-- Checker-owned source sites rebuilt by argument contraction. -/
def sourceSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    AllAppliedSites source wire :=
  applied.result.sites

def targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (site : Fin applied.sourceSites.sites.length) :
    applied.result.target.val.NodeId :=
  applied.result.targetNode site

theorem sourceWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    (source.val.wires wire).sig = .rel applied.sourceArgumentList :=
  applied.sourceSignature

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

/-- Checker-owned typed duplication witness used by cancellation transport. -/
def duplicationEvidence
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    ArgumentsSemantics.TypedArguments.DuplicationEvidence
      applied.argumentResult.targetArguments applied.sourceArgumentList :=
  applied.ledger.retraction

/-- Checker-owned argument factorization used by cancellation transport. -/
def argumentFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :=
  applied.ledger.factorization

def nodeEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    Data.Finite.FiniteEquiv source.val.NodeId applied.target.val.NodeId :=
  applied.result.nodeEquiv applied.targetSites

def wireEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    Data.Finite.FiniteEquiv source.val.WireId applied.target.val.WireId :=
  applied.result.wireEquivHeadOnly applied.source_removed_exact
    applied.local_count_exact

@[simp] theorem wireEquiv_head
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    applied.wireEquiv wire = applied.targetWire := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly
  simp
  rfl

theorem nodeEquiv_generated
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (site : Fin applied.result.sites.sites.length) :
    applied.nodeEquiv (applied.result.sites.sites.get site).node =
      applied.result.targetNode site := by
  have generated : (applied.result.sites.sites.get site).node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨applied.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage
      (applied.result.sites.sites.get site).node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_pos generated]
  rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get
    applied.result.sites site generated]

theorem nodeEquiv_generated_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (node : source.val.NodeId)
    (generated : node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    applied.nodeEquiv node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.targetSites := by
  let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
    applied.sourceSites node generated
  have sourceExact : (applied.sourceSites.sites.get site).node = node :=
    ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
      applied.sourceSites node generated
  rw [← sourceExact]
  change applied.nodeEquiv (applied.result.sites.sites.get site).node ∈ _
  rw [applied.nodeEquiv_generated site]
  exact applied.result.generatedNode_targetSiteNode applied.targetSites site

theorem nodeEquiv_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (node : source.val.NodeId)
    (retained : node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites) :
    applied.nodeEquiv node =
      applied.result.retainedNodeImage node retained := by
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retained]

theorem wireEquiv_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.wireEquiv sourceWire =
      applied.result.retainedWireImage sourceWire (by
        rw [applied.source_removed_exact]
        simpa [different]) := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
  change (if same : sourceWire = wire then applied.result.targetWire
    else applied.result.retainedWireImage sourceWire _) = _
  rw [dif_neg different]

theorem wireEquiv_retained_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  rw [applied.wireEquiv_retained sourceWire different]
  exact applied.result.retainedWireImage_signature sourceWire _

theorem wireEquiv_retained_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).scope =
      applied.result.regionEquiv (source.val.wires sourceWire).scope := by
  rw [applied.wireEquiv_retained sourceWire different,
    show
      (applied.target.val.wires
          (applied.result.retainedWireImage sourceWire _)).scope =
        applied.result.regionImage (source.val.wires sourceWire).scope by
      exact applied.result.retainedWireImage_scope sourceWire _]
  exact applied.result.regionImage_exact _

theorem targetArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    applied.result.targetArguments =
      ConcreteWirePrimitive.eraseAt applied.sourceArgumentList (position + 1) :=
  applied.target_arguments_exact

def targetArgumentList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) : List Sig :=
  applied.result.targetArguments

/-- Every generated contract application uses the exact checker-owned attachment
vector at its source-site position. -/
theorem siteArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (site : Fin applied.result.sites.sites.length) :
    applied.result.spec.arguments site =
      existingReferences
        (ConcreteWirePrimitive.eraseAt
          (applied.result.sites.sites.get site).arguments (position + 1)) :=
  applied.arguments_exact site

/-- A generated drop argument endpoint is owned by the checked image of the
exact attachment selected at that output position. -/
theorem generatedArgument_endpointOwner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (site : Fin applied.result.sites.sites.length)
    (targetPosition : Nat)
    (targetBound : targetPosition < applied.result.targetArguments.length)
    (sourceWire : source.val.WireId)
    (selected : (applied.result.spec.arguments site)[targetPosition]? =
      some (.existing sourceWire)) :
    applied.target.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg targetPosition⟩ =
      some (applied.wireEquiv sourceWire) := by
  by_cases different : sourceWire ≠ wire
  · have retained : sourceWire ∉ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simpa [different]
    have owner := applied.result.generatedArgument_endpointOwner site
      targetPosition targetBound sourceWire selected retained
    simpa [AppliedArgContract.wireEquiv,
      ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly,
      ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly, different]
      using owner
  · have same : sourceWire = wire := Classical.not_not.mp different
    subst sourceWire
    rw [applied.wireEquiv_head]
    change applied.result.checked.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg targetPosition⟩ =
      some applied.result.targetWire
    rw [applied.result.targetNode_argument_owner site targetPosition
      targetBound]
    congr 1
    unfold ConcreteWirePrimitive.replacementOwner
      ConcreteWirePrimitive.replacementNode
    simp only [Fin.addCases_right]
    rw [selected]
    simp only
    rw [ConcreteWirePrimitive.retainedReplacementWire?_head_none]
    exact applied.result.targetWire_exact.symm

/-- Public list-indexed form of generated contract endpoint ownership. -/
theorem generatedArgument_endpointOwner_of_selected
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (site : Fin applied.sourceSites.sites.length)
    (targetPosition : Nat)
    (targetBound : targetPosition < applied.targetArgumentList.length)
    (sourceWire : source.val.WireId)
    (selected :
      (ConcreteWirePrimitive.eraseAt
        (applied.sourceSites.sites.get site).arguments (position + 1))[
          targetPosition]? = some sourceWire) :
    applied.target.val.endpointOwner?
        ⟨applied.targetNode site, .arg targetPosition⟩ =
      some (applied.wireEquiv sourceWire) := by
  apply applied.generatedArgument_endpointOwner site targetPosition
    targetBound sourceWire
  rw [applied.siteArguments_exact site]
  unfold existingReferences
  rw [List.getElem?_map, show
    (ConcreteWirePrimitive.eraseAt
      (applied.result.sites.sites.get site).arguments (position + 1))[
        targetPosition]? = some sourceWire by
      simpa [sourceSites] using selected]
  rfl

/-- Exact target image of any source wire through argument contraction.  The acted
head is replaced by the checked target head; every other wire is transported
by the replacement receipt's retained-wire map. -/
def transportWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (sourceWire : source.val.WireId) :
    applied.target.val.WireId :=
  if same : sourceWire = wire then
    applied.targetWire
  else
    applied.result.retainedWireImage sourceWire (by
      rw [applied.source_removed_exact]
      simpa [same])

theorem transportWire_eq_wireEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (sourceWire : source.val.WireId) :
    applied.transportWire sourceWire = applied.wireEquiv sourceWire := by
  unfold transportWire wireEquiv
    ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly
  rfl

/-- Pushing an endpoint of a retained node through argument contraction preserves
its port and incidence on the exact transported wire. -/
theorem retainedEndpointImage_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (sourceWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires sourceWire).endpoints)
    (retained : endpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    (⟨applied.nodeEquiv endpoint.node, endpoint.port⟩ :
      CEndpoint applied.target.val.nodeCount) ∈
      (applied.target.val.wires
        (applied.wireEquiv sourceWire)).endpoints := by
  have sourceWireDifferent : sourceWire ≠ wire := by
    intro same
    subst sourceWire
    have removed : wire ∈ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simp
    exact retained (applied.result.sourceRemovedExhausted wire removed
      endpoint incident)
  have sourceRetained : sourceWire ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [sourceWireDifferent]
  have targetIncident := applied.result.retainedNode_forwardIncident
    endpoint.node retained endpoint.port sourceWire incident
  have nodeImage := applied.nodeEquiv_retained endpoint.node retained
  have wireImage := applied.wireEquiv_retained sourceWire sourceWireDifferent
  have contextImage := applied.result.contextWireMap_retained sourceWire
    sourceRetained
  rw [contextImage, ← wireImage] at targetIncident
  simpa [nodeImage] using targetIncident

/-- Pulling an endpoint of a retained rebuilt node through argument contraction
preserves its port and recovers incidence on the exact source wire. -/
theorem retainedEndpointInverse_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position)
    (sourceWire : source.val.WireId)
    (candidate : CEndpoint applied.target.val.nodeCount)
    (incident : candidate ∈
      (applied.target.val.wires
        (applied.wireEquiv sourceWire)).endpoints)
    (retained : applied.nodeEquiv.symm candidate.node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    (⟨applied.nodeEquiv.symm candidate.node, candidate.port⟩ :
      CEndpoint source.val.nodeCount) ∈
      (source.val.wires sourceWire).endpoints := by
  let sourceNode := applied.nodeEquiv.symm candidate.node
  have nodeRecover : applied.nodeEquiv sourceNode = candidate.node :=
    applied.nodeEquiv.right_inv candidate.node
  have targetRequired : candidate.port ∈
      applied.target.val.requiredPorts candidate.node :=
    ConcreteDiagram.incident_port_required definitions applied.target.val
      applied.target.property (applied.wireEquiv sourceWire) candidate incident
  have targetNodeImage : applied.result.retainedNodeImage sourceNode retained =
      candidate.node := by
    rw [← applied.nodeEquiv_retained sourceNode retained]
    exact nodeRecover
  have sourceRequired : candidate.port ∈
      source.val.requiredPorts sourceNode := by
    have retainedData : applied.target.val.nodes
        (applied.result.retainedNodeImage sourceNode retained) =
          (source.val.nodes sourceNode).rename applied.result.regionEquiv :=
      applied.result.retainedNodeImage_data sourceNode retained
    rw [ConcreteDiagram.requiredPorts] at targetRequired ⊢
    rw [← targetNodeImage, retainedData] at targetRequired
    cases sourceData : source.val.nodes sourceNode <;>
      simp [sourceData, CNode.rename] at targetRequired ⊢
    all_goals exact targetRequired
  obtain ⟨actualWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete definitions source.val
      source.property sourceNode candidate.port sourceRequired
  have actualDifferent : actualWire ≠ wire := by
    intro same
    subst actualWire
    have actualIncident := ConcreteDiagram.endpointOwner?_incident source.val
      ⟨sourceNode, candidate.port⟩ wire sourceOwner
    have removed : wire ∈ applied.result.sourceRemovedWires := by
      rw [applied.source_removed_exact]
      simp
    exact retained (applied.result.sourceRemovedExhausted wire removed
      ⟨sourceNode, candidate.port⟩ actualIncident)
  have actualRetained : actualWire ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [actualDifferent]
  have forwardOwner := applied.result.retainedNodeImage_endpointOwner
    sourceNode retained candidate.port sourceRequired actualWire sourceOwner
  change applied.target.val.endpointOwner?
      ⟨applied.result.retainedNodeImage sourceNode retained,
        candidate.port⟩ =
    some (applied.result.retainedWireImage actualWire actualRetained)
    at forwardOwner
  have targetOwner : applied.target.val.endpointOwner? candidate =
      some (applied.wireEquiv sourceWire) :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions
      applied.target.val applied.target.property candidate.node candidate.port
      targetRequired (applied.wireEquiv sourceWire) incident
  rw [targetNodeImage, targetOwner,
    ← applied.wireEquiv_retained actualWire actualDifferent]
    at forwardOwner
  have actualExact : actualWire = sourceWire :=
    applied.wireEquiv.injective (Option.some.inj forwardOwner).symm
  subst actualWire
  exact ConcreteDiagram.endpointOwner?_incident source.val
    ⟨sourceNode, candidate.port⟩ sourceWire sourceOwner

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgContract source wire position) : StepTag :=
  .argContract

end AppliedArgContract

def applyArgDuplicate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except WireArgumentError
      (AppliedArgDuplicate source wire position) :=
  match accepted : ConcreteWirePrimitive.argDuplicate source wire position with
  | .error error => .error (.concreteRejected error)
  | .ok result =>
      match sourceSignature : (source.val.wires wire).sig with
      | .iota => .error .semanticLedgerRejected
      | .rel sourceArguments =>
          match ArgumentsSemantics.checkDuplicateLedger result sourceArguments
              sourceSignature position with
          | none => .error .semanticLedgerRejected
          | some ledger =>
              let construction :=
                ConcreteWirePrimitive.argDuplicate_construction_exact source
                  wire sourceArguments sourceSignature position result accepted
              .ok ⟨result, sourceArguments, sourceSignature,
                construction.1, construction.2.1, construction.2.2.1,
                construction.2.2.2.1, construction.2.2.2.2, ledger⟩

def applyArgContract
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except WireArgumentError
      (AppliedArgContract source wire position) :=
  match accepted : ConcreteWirePrimitive.argContract source wire position with
  | .error error => .error (.concreteRejected error)
  | .ok result =>
      match sourceSignature : (source.val.wires wire).sig with
      | .iota => .error .semanticLedgerRejected
      | .rel sourceArguments =>
          match ArgumentsSemantics.checkContractLedger result sourceArguments
              sourceSignature position with
          | none => .error .semanticLedgerRejected
          | some ledger =>
              let construction :=
                ConcreteWirePrimitive.argContract_construction_exact source
                  wire sourceArguments sourceSignature position result accepted
              .ok ⟨result, sourceArguments, sourceSignature,
                construction.1, construction.2.1, construction.2.2.1,
                construction.2.2.2, ledger⟩


theorem arg_duplicate_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (applied : AppliedArgDuplicate source wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/-- Checked equal-adjacent contraction is a full-model equivalence. -/
theorem arg_contract_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (applied : AppliedArgContract source wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

end Arguments

end WirePrimitive

end VisualProof
