import VisualProof.Rule.WirePrimitive.Site
import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.IsomorphismSearch

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

/-- Stable concrete refusal outcomes for argument-plumbing primitives. -/
inductive ArgumentError
  | expectedRelation
  | nonAppliedEndpoint
  | invalidPosition
  | invalidPermutation
  | unequalAdjacentSignatures
  | unequalAdjacentAttachments
  | unshiftWireNotLocal
  | unshiftWireNotExhausted
  | attachmentCoverage
  | attachmentSignature
  | attachmentInvisible
  | invalidRemoval
  | malformedTarget (error : WFError)
  deriving Repr, DecidableEq

private def siteNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    List source.val.NodeId :=
  sites.sites.map AppliedSite.node

private def relationArguments?
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) : Option (List Sig) :=
  match (source.val.wires wire).sig with
  | .iota => none
  | .rel arguments => some arguments

private def validPosition (arguments : List α) (position : Nat) : Bool :=
  position < arguments.length

private def validInsertionPosition
    (arguments : List α) (position : Nat) : Bool :=
  position ≤ arguments.length

private def validPermutation
    (length : Nat) (permutation : List Nat) : Bool :=
  permutation.length = length &&
    permutation.Nodup &&
    permutation.all fun position => position < length

/-- Remove one position, leaving an out-of-range list unchanged. -/
def eraseAt : List α → Nat → List α
  | [], _ => []
  | _ :: tail, 0 => tail
  | head :: tail, position + 1 =>
      head :: eraseAt tail position

/-- Insert one value at a position, appending when the position is exhausted. -/
def insertAt : List α → Nat → α → List α
  | [], _, value => [value]
  | values, 0, value => value :: values
  | head :: tail, position + 1, value =>
      head :: insertAt tail position value

/-- Select the requested positions in order. -/
def permute (values : List α) (permutation : List Nat) : List α :=
  permutation.filterMap fun position => values[position]?

/-- One argument in a rebuilt applied end. -/
private inductive ArgumentReference
    (source : CheckedDiagram definitions) (localCount : Nat)
  | existing (wire : source.val.WireId)
  | local (wire : Fin localCount)
  deriving DecidableEq

/--
Checker-owned description of one simultaneous all-end replacement. Existing
attachments name source wires; local attachments name fresh wires appended
after the replacement head.
-/
private structure ReplacementSpec
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire) where
  targetArguments : List Sig
  removedWires : List source.val.WireId
  localCount : Nat
  localSignature : Fin localCount → Sig
  localScope : Fin localCount → source.val.RegionId
  arguments :
    Fin sites.sites.length →
      List (ArgumentReference source localCount)

private structure ReplacementPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites) where
  removal :
    Internal.BatchRemovalPlan source [] (siteNodes sites)
      (wire :: spec.removedWires)

private def replacementBase
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

private def retainedRegion
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    Fin (Internal.retainedRegions source []).length :=
  Internal.retainedRegionIndex source [] region (by
    unfold Internal.retainedRegions
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by simp⟩)

private def replacementNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (site : Fin sites.sites.length) :
    Fin ((replacementBase plan).nodeCount + sites.sites.length) :=
  Fin.natAdd (replacementBase plan).nodeCount site

private def existingArgumentEndpoints
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (candidate :
      Fin (Internal.retainedWires source
        (wire :: spec.removedWires)).length) :
    List
      (CEndpoint
        ((replacementBase plan).nodeCount + sites.sites.length)) :=
  let sourceWire :=
    Internal.sourceRetainedWire source (wire :: spec.removedWires) candidate
  (Data.Finite.allFin sites.sites.length).flatMap fun site =>
    (spec.arguments site).zipIdx.filterMap fun pair =>
      match pair.1 with
      | .existing argument =>
          if argument = sourceWire then
            some
              { node := replacementNode plan site
                port := .arg pair.2 }
          else
            none
      | .local _ => none

private def localArgumentEndpoints
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (freshLocal : Fin spec.localCount) :
    List
      (CEndpoint
        ((replacementBase plan).nodeCount + sites.sites.length)) :=
  (Data.Finite.allFin sites.sites.length).flatMap fun site =>
    (spec.arguments site).zipIdx.filterMap fun pair =>
      match pair.1 with
      | .existing _ => none
      | .local argument =>
          if argument = freshLocal then
            some
              { node := replacementNode plan site
                port := .arg pair.2 }
          else
            none

private def replacementCandidate
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    ConcreteDiagram definitions.length :=
  let base := replacementBase plan
  {
    regionCount := base.regionCount
    nodeCount := base.nodeCount + sites.sites.length
    wireCount := base.wireCount + (1 + spec.localCount)
    root := base.root
    regions := base.regions
    nodes :=
      Fin.addCases base.nodes fun site =>
        .atom
          (retainedRegion source (sites.sites.get site).region)
          spec.targetArguments
    wires :=
      Fin.addCases
        (fun candidate =>
          let data := base.wires candidate
          { sig := data.sig
            scope := data.scope
            endpoints :=
              (data.endpoints.map fun endpoint =>
                { node := Fin.castAdd sites.sites.length endpoint.node
                  port := endpoint.port }) ++
                existingArgumentEndpoints plan candidate })
        (fun added =>
          Fin.addCases
            (fun _ =>
              show
                CWire base.regionCount
                  (base.nodeCount + sites.sites.length)
              from
                { sig := .rel spec.targetArguments
                  scope :=
                    retainedRegion source (source.val.wires wire).scope
                  endpoints :=
                    (Data.Finite.allFin sites.sites.length).map fun site =>
                      { node := replacementNode plan site
                        port := .head } })
            (fun freshLocal =>
              show
                  CWire base.regionCount
                    (base.nodeCount + sites.sites.length)
                from
                  { sig := spec.localSignature freshLocal
                    scope := retainedRegion source (spec.localScope freshLocal)
                    endpoints := localArgumentEndpoints plan freshLocal })
            added)
  }

private def replacementCandidateWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec) :
    (replacementCandidate plan).WireId :=
  ⟨(replacementBase plan).wireCount, by
    simp only [replacementCandidate]
    omega⟩

private def replacementCandidateLocalWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : ReplacementSpec source wire sites}
    (plan : ReplacementPlan source wire sites spec)
    (fresh : Fin spec.localCount) :
    (replacementCandidate plan).WireId :=
  Fin.natAdd (replacementBase plan).wireCount
    (Fin.natAdd 1 fresh)

/-- Opaque checked result shared by the seven argument transformations. -/
structure ArgumentResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : AllAppliedSites source wire
  checked : CheckedDiagram definitions
  private spec : ReplacementSpec source wire sites
  private plan : ReplacementPlan source wire sites spec
  private generated : checked.val = replacementCandidate plan
  targetWire : checked.val.WireId
  private targetWire_exact :
    targetWire =
      Internal.checkedWire generated (replacementCandidateWire plan)

namespace ArgumentResult

/-- The checker-produced target diagram. -/
def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    CheckedDiagram definitions :=
  result.checked

/-- The checker-selected target relation argument vector. -/
def targetArguments
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List Sig :=
  result.spec.targetArguments

/-- Source wires deleted by the simultaneous replacement, including its head. -/
def sourceRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List source.val.WireId :=
  wire :: result.spec.removedWires

/-- Fresh target-local argument wires introduced by arity shift. -/
def targetLocalWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List result.checked.val.WireId :=
  (Data.Finite.allFin result.spec.localCount).map fun fresh =>
    Internal.checkedWire result.generated
      (replacementCandidateLocalWire result.plan fresh)

/-- Target wires deleted to expose the exact retained common core. -/
def targetRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List result.checked.val.WireId :=
  result.targetWire :: result.targetLocalWires

/-- Every accepted replacement consumes every applied end of the source. -/
theorem siteCount
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    result.sites.sites.length =
      (source.val.wires wire).endpoints.length :=
  result.sites.length

/-- The fresh replacement head has the checker-selected relation signature. -/
theorem targetWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    (result.checked.val.wires result.targetWire).sig =
      .rel result.targetArguments := by
  rw [result.targetWire_exact,
    Internal.checkedWire_signature_transport result.generated]
  have targetExact :
      replacementCandidateWire result.plan =
        Fin.natAdd (replacementBase result.plan).wireCount
          (0 : Fin (1 + result.spec.localCount)) := by
    apply Fin.ext
    rfl
  rw [targetExact]
  simp only [replacementCandidate, Fin.addCases_right]
  have zeroExact :
      (0 : Fin (1 + result.spec.localCount)) =
        Fin.castAdd result.spec.localCount (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [zeroExact]
  rfl

end ArgumentResult

private def replaceAppliedEnds
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : ReplacementSpec source wire sites) :
    Except ArgumentError (ArgumentResult source wire) := by
  match Internal.checkBatchRemovalPlan?
      source [] (siteNodes sites) (wire :: spec.removedWires) with
  | none => exact .error .invalidRemoval
  | some removal =>
      let plan : ReplacementPlan source wire sites spec := ⟨removal⟩
      let candidate := replacementCandidate plan
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error => exact .error (.malformedTarget error)
      | .ok checked =>
          have generated : checked.val = candidate :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          exact .ok
            (ArgumentResult.mk sites checked spec plan generated
              (Internal.checkedWire generated
                (replacementCandidateWire plan))
              rfl)

private def checkedSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ArgumentError (AllAppliedSites source wire) :=
  match checkAllAppliedSites source wire with
  | none => .error .nonAppliedEndpoint
  | some sites => .ok sites

private def checkedRelationArguments
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ArgumentError (List Sig) :=
  match relationArguments? source wire with
  | none => .error .expectedRelation
  | some arguments => .ok arguments

private def existingReferences
    {source : CheckedDiagram definitions}
    {localCount : Nat}
    (arguments : List source.val.WireId) :
    List (ArgumentReference source localCount) :=
  arguments.map .existing

/-- Add one locally scoped fresh argument at every applied end. -/
def arityShift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  let sites ← checkedSites source wire
  let spec : ReplacementSpec source wire sites :=
    { targetArguments := relationArguments ++ [newArgument]
      removedWires := []
      localCount := sites.sites.length
      localSignature := fun _ => newArgument
      localScope := fun site => (sites.sites.get site).region
      arguments := fun site =>
        existingReferences (sites.sites.get site).arguments ++
          [.local site] }
  replaceAppliedEnds source wire sites spec

private def localUnshiftWires?
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (position : Nat) :
    Except ArgumentError (List source.val.WireId) := by
  let selected := sites.sites.map fun site => site.arguments[position]?
  if selected.any Option.isNone then
    exact .error .invalidPosition
  else
    let locals := selected.filterMap id
    if (sites.sites.zip locals).all (fun pair =>
        (source.val.wires pair.2).scope == pair.1.region) then
      if (sites.sites.zip locals).all (fun pair =>
          (source.val.wires pair.2).endpoints ==
            [⟨pair.1.node, .arg position⟩]) then
        exact .ok locals
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
  let sites ← checkedSites source wire
  let locals ← localUnshiftWires? sites position
  let spec : ReplacementSpec source wire sites :=
    { targetArguments := eraseAt relationArguments position
      removedWires := locals
      localCount := 0
      localSignature := Fin.elim0
      localScope := Fin.elim0
      arguments := fun site =>
        existingReferences <|
          eraseAt (sites.sites.get site).arguments position }
  replaceAppliedEnds source wire sites spec

/-- Reorder every applied argument tuple by one checked permutation. -/
def argPermute
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (permutation : List Nat) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validPermutation relationArguments.length permutation then
    throw .invalidPermutation
  let sites ← checkedSites source wire
  let spec : ReplacementSpec source wire sites :=
    { targetArguments := permute relationArguments permutation
      removedWires := []
      localCount := 0
      localSignature := Fin.elim0
      localScope := Fin.elim0
      arguments := fun site =>
        existingReferences <|
          permute (sites.sites.get site).arguments permutation }
  replaceAppliedEnds source wire sites spec

/-- Duplicate one position directly after itself at every applied end. -/
def argDuplicate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validPosition relationArguments position then
    throw .invalidPosition
  let sites ← checkedSites source wire
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
  replaceAppliedEnds source wire sites spec

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
  let sites ← checkedSites source wire
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
  replaceAppliedEnds source wire sites spec

/-- Drop one argument position at every applied end. -/
def argDrop
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except ArgumentError (ArgumentResult source wire) := do
  let relationArguments ← checkedRelationArguments source wire
  if !validPosition relationArguments position then
    throw .invalidPosition
  let sites ← checkedSites source wire
  let spec : ReplacementSpec source wire sites :=
    { targetArguments := eraseAt relationArguments position
      removedWires := []
      localCount := 0
      localSignature := Fin.elim0
      localScope := Fin.elim0
      arguments := fun site =>
        existingReferences <|
          eraseAt (sites.sites.get site).arguments position }
  replaceAppliedEnds source wire sites spec

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
  let sites ← checkedSites source wire
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
  replaceAppliedEnds source wire sites spec

end ConcreteWirePrimitive

end VisualProof
