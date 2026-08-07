import VisualProof.Concrete.Operation.Structural

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open VisualProof.Data.Finite
open Diagram

def abstractionRegions (occurrences : List (OperationAbstractionOccurrence input)) :
    List (Fin input.val.regionCount) :=
  occurrences.flatMap fun occurrence => occurrence.selection.selectedRegions

def abstractionNodes (occurrences : List (OperationAbstractionOccurrence input)) :
    List (Fin input.val.nodeCount) :=
  occurrences.flatMap fun occurrence => occurrence.selection.selectedNodes

def abstractionWires (occurrences : List (OperationAbstractionOccurrence input)) :
    List (Fin input.val.wireCount) :=
  occurrences.flatMap fun occurrence => occurrence.selection.internalWires

structure AbstractionDomains (input : Checked )
    (occurrences : List (OperationAbstractionOccurrence input)) where
  regions : SurvivorDomain input.val.regionCount :=
    ⟨fun region => decide (region ∉ abstractionRegions occurrences)⟩
  regions_exact : ∀ region, regions.survives region =
      decide (region ∉ abstractionRegions occurrences) := by
    intro region
    rfl
  nodes : SurvivorDomain input.val.nodeCount :=
    ⟨fun node => decide (node ∉ abstractionNodes occurrences)⟩
  nodes_exact : ∀ node, nodes.survives node =
      decide (node ∉ abstractionNodes occurrences) := by
    intro node
    rfl
  wires : SurvivorDomain input.val.wireCount :=
    ⟨fun wire => decide (wire ∉ abstractionWires occurrences)⟩
  wires_exact : ∀ wire, wires.survives wire =
      decide (wire ∉ abstractionWires occurrences) := by
    intro wire
    rfl

/-- The canonical survivor domains used by comprehension abstraction. -/
def abstractionDomains (input : Checked )
    (occurrences : List (OperationAbstractionOccurrence input)) :
    AbstractionDomains input occurrences := {}

def abstractRegion? (input : Checked )
    (wrap : CheckedSelection input.val)
    (occurrences : List (OperationAbstractionOccurrence input))
    (domains : AbstractionDomains input occurrences)
    (bubble : Fin (domains.regions.count + 1))
    (original : Fin input.val.regionCount) :
    Option (CRegion (domains.regions.count + 1)) :=
  match input.val.regions original with
  | .sheet => some .sheet
  | .cut parent =>
      if original ∈ wrap.val.childRoots then
        some (.cut bubble)
      else
        (domains.regions.index? parent).map fun mapped => .cut mapped.castSucc
  | .bubble parent arity =>
      if original ∈ wrap.val.childRoots then
        some (.bubble bubble arity)
      else
        (domains.regions.index? parent).map fun mapped =>
          .bubble mapped.castSucc arity

def abstractNode? (input : Checked )
    (wrap : CheckedSelection input.val)
    (occurrences : List (OperationAbstractionOccurrence input))
    (domains : AbstractionDomains input occurrences)
    (bubble : Fin (domains.regions.count + 1))
    (original : Fin input.val.nodeCount) :
    Option (CNode (domains.regions.count + 1)) :=
  let owner? (owner : Fin input.val.regionCount) :=
    if original ∈ wrap.val.directNodes then some bubble
    else (domains.regions.index? owner).map Fin.castSucc
  match input.val.nodes original with
  | .identity owner arity =>
      (owner? owner).map fun mapped => .identity mapped arity
  | .atom owner binder => do
      let mappedOwner ← owner? owner
      let mappedBinder ← domains.regions.index? binder
      pure (.atom mappedOwner mappedBinder.castSucc)
def abstractFrameEndpoints
    (input : Checked )
    (occurrences : List (OperationAbstractionOccurrence input))
    (domains : AbstractionDomains input occurrences)
    (wire : domains.wires.Carrier) :
    List (CEndpoint (domains.nodes.count + occurrences.length)) :=
  (input.val.wires (domains.wires.origin wire)).endpoints.filterMap fun endpoint =>
    (domains.nodes.reindexEndpoint? endpoint).map fun mapped =>
      { node := mapped.node.castAdd occurrences.length, port := mapped.port }

def abstractAtomEndpoints
    (input : Checked )
    (occurrences : List (OperationAbstractionOccurrence input))
    (domains : AbstractionDomains input occurrences)
    (wire : domains.wires.Carrier) :
    List (CEndpoint (domains.nodes.count + occurrences.length)) :=
  (allFin occurrences.length).flatMap fun occurrenceIndex =>
    let occurrence := occurrences.get occurrenceIndex
    (allFin occurrence.args.length).filterMap fun argumentIndex =>
      if occurrence.args.get argumentIndex = domains.wires.origin wire then
        some {
          node := Fin.natAdd domains.nodes.count occurrenceIndex
          port := .arg argumentIndex.val
        }
      else none

def comprehensionAbstractRaw?
    (input : Checked )
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpen )
    (occurrences : List (OperationAbstractionOccurrence input)) :
    Option { raw : Concrete.Diagram //
      raw.wireCount = ({} : AbstractionDomains input occurrences).wires.count } := do
  let domains := abstractionDomains input occurrences
  let bubble : Fin (domains.regions.count + 1) := Fin.last domains.regions.count
  let rootBase ← domains.regions.index? input.val.root
  let parentBase ← domains.regions.index? wrap.val.anchor
  let regions ← sequenceFin fun region =>
    abstractRegion? input wrap occurrences domains bubble
      (domains.regions.origin region)
  let nodes ← sequenceFin fun node =>
    abstractNode? input wrap occurrences domains bubble
      (domains.nodes.origin node)
  let atomOwners ← sequenceFin fun index =>
    let anchor := (occurrences.get index).selection.val.anchor
    if anchor = wrap.val.anchor then some bubble
    else (domains.regions.index? anchor).map Fin.castSucc
  let wires ← sequenceFin fun wire => do
    let scopeBase ← domains.regions.index?
      (input.val.wires (domains.wires.origin wire)).scope
    pure {
      scope := scopeBase.castSucc
      endpoints := abstractFrameEndpoints input occurrences domains wire ++
        abstractAtomEndpoints input occurrences domains wire
    }
  pure ⟨{
    regionCount := domains.regions.count + 1
    nodeCount := domains.nodes.count + occurrences.length
    wireCount := domains.wires.count
    root := rootBase.castSucc
    regions := Fin.lastCases
      (.bubble parentBase.castSucc comprehension.val.boundary.length) regions
    nodes := Fin.addCases nodes fun index => .atom (atomOwners index) bubble
    wires := wires
  }, rfl⟩

/-- Proof-relevant execution trace for the batch abstraction constructor.
This exposes the exact successful choices made by the authoritative raw
executor without introducing a second graph transformation. -/
structure AbstractionRawTrace
    (input : Checked )
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpen )
    (occurrences : List (OperationAbstractionOccurrence input))
    (raw : Concrete.Diagram) where
  rootBase : Fin (abstractionDomains input occurrences).regions.count
  parentBase : Fin (abstractionDomains input occurrences).regions.count
  regions : Fin (abstractionDomains input occurrences).regions.count →
    CRegion ((abstractionDomains input occurrences).regions.count + 1)
  nodes : Fin (abstractionDomains input occurrences).nodes.count →
    CNode ((abstractionDomains input occurrences).regions.count + 1)
  atomOwners : Fin occurrences.length →
    Fin ((abstractionDomains input occurrences).regions.count + 1)
  wires : Fin (abstractionDomains input occurrences).wires.count →
    CWire ((abstractionDomains input occurrences).regions.count + 1)
      ((abstractionDomains input occurrences).nodes.count +
        occurrences.length)
  root_result :
    (abstractionDomains input occurrences).regions.index? input.val.root =
      some rootBase
  parent_result :
    (abstractionDomains input occurrences).regions.index?
        wrap.val.anchor = some parentBase
  regions_result :
    sequenceFin (fun region =>
      abstractRegion? input wrap occurrences
        (abstractionDomains input occurrences)
        (Fin.last (abstractionDomains input occurrences).regions.count)
        ((abstractionDomains input occurrences).regions.origin region)) =
      some regions
  nodes_result :
    sequenceFin (fun node =>
      abstractNode? input wrap occurrences
        (abstractionDomains input occurrences)
        (Fin.last (abstractionDomains input occurrences).regions.count)
        ((abstractionDomains input occurrences).nodes.origin node)) =
      some nodes
  atomOwners_result :
    sequenceFin (fun index =>
      let anchor := (occurrences.get index).selection.val.anchor
      if anchor = wrap.val.anchor then
        some (Fin.last
          (abstractionDomains input occurrences).regions.count)
      else
        ((abstractionDomains input occurrences).regions.index? anchor).map
          Fin.castSucc) = some atomOwners
  wires_result :
    sequenceFin (fun wire => do
      let scopeBase ← (abstractionDomains input occurrences).regions.index?
        (input.val.wires
          ((abstractionDomains input occurrences).wires.origin wire)).scope
      pure {
        scope := scopeBase.castSucc
        endpoints := abstractFrameEndpoints input occurrences
            (abstractionDomains input occurrences) wire ++
          abstractAtomEndpoints input occurrences
            (abstractionDomains input occurrences) wire
      }) = some wires
  raw_eq : raw = {
    regionCount :=
      (abstractionDomains input occurrences).regions.count + 1
    nodeCount := (abstractionDomains input occurrences).nodes.count +
      occurrences.length
    wireCount := (abstractionDomains input occurrences).wires.count
    root := rootBase.castSucc
    regions := Fin.lastCases
      (.bubble parentBase.castSucc comprehension.val.boundary.length) regions
    nodes := Fin.addCases nodes fun index => .atom (atomOwners index)
      (Fin.last (abstractionDomains input occurrences).regions.count)
    wires := wires
  }

/-- Every accepted raw abstraction result carries its exact constructor
trace. -/
theorem comprehensionAbstractRaw?_trace
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw) :
    Nonempty (AbstractionRawTrace input wrap comprehension occurrences raw) := by
  rw [Option.map_eq_some_iff] at hraw
  obtain ⟨result, built, rawEq⟩ := hraw
  subst raw
  unfold comprehensionAbstractRaw? at built
  let domains := abstractionDomains input occurrences
  let bubble : Fin (domains.regions.count + 1) := Fin.last domains.regions.count
  change (domains.regions.index? input.val.root).bind (fun rootBase =>
    (domains.regions.index? wrap.val.anchor).bind (fun parentBase =>
    (sequenceFin fun region =>
      abstractRegion? input wrap occurrences domains bubble
        (domains.regions.origin region)).bind (fun regions =>
    (sequenceFin fun node =>
      abstractNode? input wrap occurrences domains bubble
        (domains.nodes.origin node)).bind (fun nodes =>
    (sequenceFin fun index =>
      let anchor := (occurrences.get index).selection.val.anchor
      if anchor = wrap.val.anchor then some bubble
      else (domains.regions.index? anchor).map Fin.castSucc).bind
        (fun atomOwners =>
    (sequenceFin fun wire => do
      let scopeBase ← domains.regions.index?
        (input.val.wires (domains.wires.origin wire)).scope
      pure {
        scope := scopeBase.castSucc
        endpoints := abstractFrameEndpoints input occurrences domains wire ++
          abstractAtomEndpoints input occurrences domains wire
      }).bind (fun wires => some ⟨{
        regionCount := domains.regions.count + 1
        nodeCount := domains.nodes.count + occurrences.length
        wireCount := domains.wires.count
        root := rootBase.castSucc
        regions := Fin.lastCases
          (.bubble parentBase.castSucc comprehension.val.boundary.length) regions
        nodes := Fin.addCases nodes fun index => .atom (atomOwners index) bubble
        wires := wires
      }, rfl⟩)))))) = some result at built
  rw [Option.bind_eq_some_iff] at built
  obtain ⟨rootBase, rootResult, built⟩ := built
  rw [Option.bind_eq_some_iff] at built
  obtain ⟨parentBase, parentResult, built⟩ := built
  rw [Option.bind_eq_some_iff] at built
  obtain ⟨regions, regionsResult, built⟩ := built
  rw [Option.bind_eq_some_iff] at built
  obtain ⟨nodes, nodesResult, built⟩ := built
  rw [Option.bind_eq_some_iff] at built
  obtain ⟨atomOwners, atomOwnersResult, built⟩ := built
  rw [Option.bind_eq_some_iff] at built
  obtain ⟨wires, wiresResult, resultEq⟩ := built
  cases resultEq
  exact ⟨{
    rootBase
    parentBase
    regions
    nodes
    atomOwners
    wires
    root_result := rootResult
    parent_result := parentResult
    regions_result := regionsResult
    nodes_result := nodesResult
    atomOwners_result := atomOwnersResult
    wires_result := wiresResult
    raw_eq := rfl
  }⟩

def comprehensionAbstractWireProvenance
    (input : Checked )
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpen )
    (occurrences : List (OperationAbstractionOccurrence input))
    (raw : Concrete.Diagram)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw) : WireProvenance input.val raw :=
  let domains := abstractionDomains input occurrences
  WireProvenance.survivors input.val raw domains.wires (by
    rw [Option.map_eq_some_iff] at hraw
    obtain ⟨witness, _, equality⟩ := hraw
    subst raw
    exact witness.property)

def comprehensionAbstractWireTransport
    (input : Checked )
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpen )
    (occurrences : List (OperationAbstractionOccurrence input))
    (raw : Concrete.Diagram)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw) : WireTransport input.val raw :=
  let domains := abstractionDomains input occurrences
  WireTransport.survivors input.val raw domains.wires (by
    rw [Option.map_eq_some_iff] at hraw
    obtain ⟨witness, _, equality⟩ := hraw
    subst raw
    exact witness.property)

def applyComprehensionAbstract (orientation : Orientation)
    (input : Checked )
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpen )
    (occurrences : List (OperationAbstractionOccurrence input))
    (_payload : OperationComprehensionAbstractPayload input wrap comprehension occurrences) :
    Except Error (OperationReceipt input) :=
  if erasurePolarity orientation
      (concreteCutDepth input.val wrap.val.anchor) then
    match hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
        Subtype.val with
    | none => .error .operationRejected
    | some raw =>
        match hcheck : checkWellFormed  raw with
        | .error error => .error (.resultNotWellFormed error)
        | .ok result => .ok (OperationReceipt.ofChecked input raw
            (comprehensionAbstractWireProvenance input wrap comprehension
              occurrences raw hraw)
            (comprehensionAbstractWireTransport input wrap comprehension
              occurrences raw hraw)
            result hcheck)
  else
    .error .wrongPolarity

theorem applyComprehensionAbstract_success_shape
    (happly : applyComprehensionAbstract orientation input wrap comprehension
      occurrences payload = .ok result) :
    ∃ raw, (comprehensionAbstractRaw? input wrap comprehension occurrences).map
        Subtype.val = some raw ∧ result.result.val = raw := by
  unfold applyComprehensionAbstract at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i raw hraw
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨raw, hraw, checkWellFormed_preserves_input hcheck⟩

theorem applyComprehensionAbstract_success
    (happly : applyComprehensionAbstract orientation input wrap comprehension
      occurrences payload = .ok result) :
    erasurePolarity orientation
        (concreteCutDepth input.val wrap.val.anchor) ∧
      ∃ raw,
        (comprehensionAbstractRaw? input wrap comprehension occurrences).map
            Subtype.val = some raw ∧
          result.result.val = raw := by
  have hpolarity : erasurePolarity orientation
      (concreteCutDepth input.val wrap.val.anchor) := by
    by_cases h : erasurePolarity orientation
        (concreteCutDepth input.val wrap.val.anchor)
    · exact h
    · simp [applyComprehensionAbstract, h] at happly
  exact ⟨hpolarity, applyComprehensionAbstract_success_shape happly⟩

theorem applyComprehensionAbstract_realizes
    (happly : applyComprehensionAbstract orientation input wrap comprehension
      occurrences payload = .ok result) :
    erasurePolarity orientation
        (concreteCutDepth input.val wrap.val.anchor) ∧
      ∃ raw,
        ∃ hraw :
            (comprehensionAbstractRaw? input wrap comprehension occurrences).map
              Subtype.val = some raw,
          result.Realizes raw
            (comprehensionAbstractWireProvenance input wrap comprehension
              occurrences raw hraw)
            (comprehensionAbstractWireTransport input wrap comprehension
              occurrences raw hraw) := by
  have hpolarity : erasurePolarity orientation
      (concreteCutDepth input.val wrap.val.anchor) := by
    by_cases h : erasurePolarity orientation
        (concreteCutDepth input.val wrap.val.anchor)
    · exact h
    · simp [applyComprehensionAbstract, h] at happly
  refine ⟨hpolarity, ?_⟩
  unfold applyComprehensionAbstract at happly
  rw [if_pos hpolarity] at happly
  split at happly <;> try contradiction
  rename_i raw hraw
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨raw, hraw, OperationReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

structure InstantiationState (origin : Checked )
    (parameterCount proxyCount : Nat) where
  diagram : Checked
  provenance : WireProvenance origin.val diagram.val
  interface : WireTransport origin.val diagram.val
  bubble : Fin diagram.val.regionCount
  parameters : Fin parameterCount → Fin diagram.val.wireCount
  binderTargets : Fin proxyCount → Fin diagram.val.regionCount
  pendingAtoms : List (Fin diagram.val.nodeCount)
  processedAtoms : List (Fin diagram.val.nodeCount)

def InstantiationState.ownedAtoms
    (state : InstantiationState origin parameterCount proxyCount) :
    List (Fin state.diagram.val.nodeCount) :=
  state.processedAtoms ++ state.pendingAtoms

private def comprehensionSpliceError : Splice.Input.Error → Error
  | .attachmentNotVisible => .boundaryMismatch
  | .duplicateBinderTarget => .binderEscape
  | .binderKindOrArityMismatch => .binderKindOrArityMismatch
  | .binderDoesNotEncloseSite => .binderDoesNotEnclose
  | .resultNotWellFormed error => .resultNotWellFormed error

def boundAtoms (input : Checked )
    (bubble : Fin input.val.regionCount) : List (Fin input.val.nodeCount) :=
  filterFin fun node =>
    match input.val.nodes node with
    | .atom _ binder => decide (binder = bubble)
    | _ => false

theorem mem_boundAtoms_iff (input : Checked )
    (bubble : Fin input.val.regionCount)
    (node : Fin input.val.nodeCount) :
    node ∈ boundAtoms input bubble ↔
      ∃ site, input.val.nodes node = .atom site bubble := by
  rw [boundAtoms, mem_filterFin]
  cases hnode : input.val.nodes node with
  | identity region arity => simp
  | atom site binder =>
      simp only [decide_eq_true_eq]
      constructor
      · intro heq
        subst binder
        exact ⟨site, rfl⟩
      · rintro ⟨candidate, heq⟩
        cases heq
        rfl
def initialInstantiationState
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders) :
    InstantiationState input attachments.length payload.binderSpine.proxyCount := {
  diagram := input
  provenance := WireProvenance.identity input.val
  interface := WireTransport.identity input.val
  bubble := bubble
  parameters := attachments.get
  binderTargets := payload.binderTargets
  pendingAtoms := boundAtoms input bubble
  processedAtoms := []
}

/-- The exact ordered host attachment seen by one comprehension copy.  The
argument prefix and transported fixed-parameter suffix are computed from the
current state, so different copies may induce different alias partitions. -/
def instantiationAttachment
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount) :
    Fin comprehension.val.boundary.length → Fin state.diagram.val.wireCount :=
  fun position =>
    Fin.addCases arguments state.parameters
      (Fin.cast payload.boundarySplit position)

/-- Repackage the original payload for one attachment-materialized copy.
Regions and the designated binder spine are unchanged; only boundary wire
identities and terminal-body identity nodes are added for this copy. -/
def materializedInstantiationPayload
    {Host : Type} [DecidableEq Host]
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (attachment : Fin comprehension.val.boundary.length → Host)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      comprehension attachment payload.binderSpine) :
    OperationComprehensionInstantiatePayload input bubble certificate.result attachments
      binders where
  parent := payload.parent
  arity := payload.arity
  bubble_eq := payload.bubble_eq
  boundarySplit := certificate.boundary_length.trans payload.boundarySplit
  parameterScopesProper := payload.parameterScopesProper
  binderSpine := certificate.spine
  terminalBody := certificate.terminalBody payload.terminalBody
  binderTargets := payload.binderTargets
  binderPairsExact := payload.binderPairsExact
  binderTargetsProper := payload.binderTargetsProper

def instantiateArguments?
    (state : InstantiationState origin p q)
    (node : Fin state.diagram.val.nodeCount) (arity : Nat) :
    Option (Fin arity → Fin state.diagram.val.wireCount) :=
  sequenceFin fun index =>
    Elaboration.endpointOwner? state.diagram.val
      { node := node, port := .arg index }

def instantiateSpliceInput {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount) :
    Splice.Input  where
  frame := state.diagram
  pattern := comprehension
  site := site
  attachment := fun position =>
    Fin.addCases arguments state.parameters
      (Fin.cast payload.boundarySplit position)
  binderSpine := payload.binderSpine
  terminalBody := payload.terminalBody
  binderTarget := state.binderTargets

/-- The exact state transition performed after one successful comprehension
splice.  Keeping this transition proof-relevant lets soundness follow the
executor's real maps instead of reconstructing a parallel copy operation. -/
def advanceInstantiationState {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    InstantiationState origin attachments.length
      payload.binderSpine.proxyCount :=
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let nextDiagram : Checked  :=
    ⟨layout.plugRaw,
      Splice.Input.PlugLayout.plugRaw_wellFormed  spliceInput layout
        hadmissible⟩
  {
    diagram := nextDiagram
    provenance := state.provenance.compose
      (spliceFrameWireProvenance spliceInput)
    interface := state.interface.compose
      (spliceFrameWireTransport spliceInput)
    bubble := layout.frameRegion state.bubble
    parameters := fun index =>
      layout.frameWire (spliceInput.quotientWire (state.parameters index))
    binderTargets := fun index =>
      layout.frameRegion (state.binderTargets index)
    pendingAtoms := tail.map layout.frameNode
    processedAtoms := state.processedAtoms.map layout.frameNode ++
      [layout.frameNode atom]
  }

/-- The exact operational splice input for one attachment-materialized copy. -/
def materializedInstantiationSpliceInput {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine) : Splice.Input  :=
  instantiateSpliceInput (input := input) (bubble := bubble)
    (origin := origin) certificate.result attachments binders
    (materializedInstantiationPayload (input := input) (bubble := bubble)
      (comprehension := comprehension) (attachments := attachments)
      (binders := binders) payload
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      certificate)
    state site arguments

/-- Attachment-aware materialization makes the operational retained-host
quotient discrete for the exact current copy.  This is intentionally an
explicit proof obligation in the contract-first layer. -/
theorem materializedInstantiationSpliceInput_respectsBoundary
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine) :
    (materializedInstantiationSpliceInput comprehension attachments binders
      payload state site arguments certificate).AttachmentsRespectBoundary := by
  intro left right hboundary
  exact ((Splice.AttachmentAliasMaterialization.raw_boundary_get_eq_iff
    comprehension.val
    (instantiationAttachment comprehension attachments binders payload state
      arguments)
    payload.binderSpine.bodyContainer
    (Fin.cast certificate.boundary_length left)
    (Fin.cast certificate.boundary_length right)).1 (by
      simpa [materializedInstantiationSpliceInput, instantiateSpliceInput,
        materializedInstantiationPayload,
        Splice.AttachmentAliasMaterialization.Certificate.result] using
        hboundary)).2

/-- The state transition driven by one exact attachment-materialized splice. -/
def advanceMaterializedInstantiationState {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine)
    (hadmissible : (materializedInstantiationSpliceInput comprehension
      attachments binders payload state site arguments certificate).Admissible) :
    InstantiationState origin attachments.length
      payload.binderSpine.proxyCount :=
  advanceInstantiationState (input := input) (bubble := bubble)
    (origin := origin) certificate.result attachments binders
    (materializedInstantiationPayload (input := input) (bubble := bubble)
      (comprehension := comprehension) (attachments := attachments)
      (binders := binders) payload
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      certificate)
    state atom tail site arguments hadmissible

/-- Proof-relevant authority for one successful copy step.  Every operational
value and equality consumed by the executor is exposed here; recursion keeps
the original comprehension and payload and advances only through `next`. -/
structure InstantiationCopyPlan {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount) where
  materialization : Splice.AttachmentAliasMaterialization.Certificate
    comprehension
    (instantiationAttachment comprehension attachments binders payload state
      arguments)
    payload.binderSpine
  materializationChecked :
    Splice.AttachmentAliasMaterialization.check comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine payload.terminalBody = .ok materialization
  attachmentsRespectBoundary :
    (materializedInstantiationSpliceInput comprehension attachments binders
      payload state site arguments materialization).AttachmentsRespectBoundary
  checkedInput : Splice.Input.CheckedInput
  checkedInputChecked :
    Splice.Input.checkInput
      (materializedInstantiationSpliceInput comprehension attachments binders
        payload state site arguments materialization) = .ok checkedInput
  next : InstantiationState origin attachments.length
    payload.binderSpine.proxyCount
  next_eq : next =
    advanceMaterializedInstantiationState comprehension attachments binders
      payload state atom tail site arguments materialization
        (Splice.Input.checkInput_sound checkedInputChecked).2

namespace InstantiationCopyPlan

def attachment {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (_plan : InstantiationCopyPlan comprehension attachments binders payload
      state atom tail site arguments) :
    Fin comprehension.val.boundary.length → Fin state.diagram.val.wireCount :=
  instantiationAttachment comprehension attachments binders payload state
    arguments

def operationalPayload {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (plan : InstantiationCopyPlan comprehension attachments binders payload
      state atom tail site arguments) :
    OperationComprehensionInstantiatePayload input bubble plan.materialization.result
      attachments binders :=
  materializedInstantiationPayload (input := input) (bubble := bubble)
    (comprehension := comprehension) (attachments := attachments)
    (binders := binders) payload
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      plan.materialization

def spliceInput {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (plan : InstantiationCopyPlan comprehension attachments binders payload
      state atom tail site arguments) : Splice.Input  :=
  materializedInstantiationSpliceInput comprehension attachments binders payload
    state site arguments plan.materialization

end InstantiationCopyPlan

/-- Construct the one-copy plan by running attachment-aware materialization and
the authoritative splice-input checker in sequence. -/
def planInstantiationCopy {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount) :
    Except Error
      (InstantiationCopyPlan comprehension attachments binders payload state
        atom tail site arguments) :=
  match hmaterialization : Splice.AttachmentAliasMaterialization.check
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine payload.terminalBody with
  | .error error => .error (.resultNotWellFormed error)
  | .ok materialization =>
      let spliceInput := materializedInstantiationSpliceInput comprehension
        attachments binders payload state site arguments materialization
      match hinput : Splice.Input.checkInput spliceInput with
      | .error error => .error (comprehensionSpliceError error)
      | .ok checkedInput =>
          have hadmissible : spliceInput.Admissible :=
            (Splice.Input.checkInput_sound hinput).2
          let next := advanceMaterializedInstantiationState comprehension
            attachments binders payload state atom tail site arguments
            materialization hadmissible
          .ok {
            materialization := materialization
            materializationChecked := hmaterialization
            attachmentsRespectBoundary :=
              materializedInstantiationSpliceInput_respectsBoundary
                comprehension attachments binders payload state site arguments
                materialization
            checkedInput := checkedInput
            checkedInputChecked := hinput
            next := next
            next_eq := rfl
          }

def instantiateCopies {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked } :
    Nat → InstantiationState origin attachments.length
      payload.binderSpine.proxyCount →
      Except Error (InstantiationState origin attachments.length
        payload.binderSpine.proxyCount)
  | 0, state =>
      if state.pendingAtoms.isEmpty then .ok state else .error .operationRejected
  | fuel + 1, state =>
      match state.pendingAtoms with
      | [] => .ok state
      | atom :: tail =>
          match state.diagram.val.nodes atom with
          | .identity .. => .error .operationRejected
          | .atom site candidate =>
              if candidate = state.bubble then
                match instantiateArguments? state atom payload.arity with
                | none => .error .boundaryMismatch
                | some arguments =>
                    match planInstantiationCopy comprehension attachments binders
                        payload state atom tail site arguments with
                    | .error error => .error error
                    | .ok plan =>
                        instantiateCopies comprehension attachments binders payload
                          fuel plan.next
              else
                .error .operationRejected

theorem instantiateCopies_success_pendingAtoms_empty
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (hcopy : instantiateCopies comprehension attachments binders payload
      state.pendingAtoms.length state = .ok result) :
    result.pendingAtoms = [] := by
  generalize hfuel : state.pendingAtoms.length = fuel at hcopy
  induction fuel generalizing state result with
  | zero =>
      have hpending : state.pendingAtoms = [] := by
        simpa using hfuel
      simp [instantiateCopies, hpending] at hcopy
      subst result
      exact hpending
  | succ fuel ih =>
      cases hpending : state.pendingAtoms with
      | nil =>
          simp [hpending] at hfuel
      | cons atom tail =>
          have htail : tail.length = fuel := by
            simpa [hpending] using hfuel
          simp only [instantiateCopies, hpending] at hcopy
          split at hcopy <;> try contradiction
          rename_i site candidate hnode
          split at hcopy <;> try contradiction
          split at hcopy <;> try contradiction
          rename_i arguments harguments
          split at hcopy <;> try contradiction
          rename_i plan hplan
          apply ih _ _ _ hcopy
          rw [plan.next_eq]
          simpa [advanceMaterializedInstantiationState,
            advanceInstantiationState] using htail

/-- A successful copy run transports the complete owned-atom list through one
composed total injective node map.  Unlike receipt provenance, this map retains
nodes through every splice and therefore records the exact removal ownership. -/
theorem instantiateCopies_success_ownedAtoms_map
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (fuel : Nat)
    (state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (hcopy : instantiateCopies comprehension attachments binders payload
      fuel state = .ok result) :
    ∃ nodeMap : Fin state.diagram.val.nodeCount →
        Fin result.diagram.val.nodeCount,
      Function.Injective nodeMap ∧
        result.ownedAtoms = state.ownedAtoms.map nodeMap ∧
        ∀ {node site},
          state.diagram.val.nodes node = .atom site state.bubble →
            ∃ resultSite,
              result.diagram.val.nodes (nodeMap node) =
                .atom resultSite result.bubble := by
  induction fuel generalizing state result with
  | zero =>
      simp only [instantiateCopies] at hcopy
      split at hcopy <;> try contradiction
      cases hcopy
      exact ⟨id, Function.injective_id, by simp, fun hnode => ⟨_, hnode⟩⟩
  | succ fuel ih =>
      simp only [instantiateCopies] at hcopy
      split at hcopy
      · cases hcopy
        exact ⟨id, Function.injective_id, by simp, fun hnode => ⟨_, hnode⟩⟩
      · rename_i atom tail hpending
        split at hcopy <;> try contradiction
        rename_i site candidate hnode
        split at hcopy <;> try contradiction
        split at hcopy <;> try contradiction
        rename_i arguments harguments
        split at hcopy <;> try contradiction
        rename_i plan hplan
        let spliceInput := plan.spliceInput
        have hadmissible : spliceInput.Admissible :=
          (Splice.Input.checkInput_sound plan.checkedInputChecked).2
        let layout := spliceInput.plugLayout
        let next := advanceMaterializedInstantiationState comprehension
          attachments binders payload state atom tail site arguments
          plan.materialization hadmissible
        rw [plan.next_eq] at hcopy
        change instantiateCopies comprehension attachments binders payload
          fuel next = .ok result at hcopy
        obtain ⟨restMap, hrestInjective, hrestOwned, hrestBound⟩ :=
          ih next result hcopy
        refine ⟨restMap ∘ layout.frameNode,
          hrestInjective.comp layout.frameNode_injective, ?_, ?_⟩
        · rw [hrestOwned]
          have hnext : next.ownedAtoms =
              state.ownedAtoms.map layout.frameNode := by
            calc
              next.ownedAtoms =
                  (state.processedAtoms.map layout.frameNode ++
                    [layout.frameNode atom]) ++ tail.map layout.frameNode := rfl
              _ = (state.processedAtoms ++ atom :: tail).map
                  layout.frameNode := by
                induction state.processedAtoms with
                | nil => rfl
                | cons head rest ih =>
                    simp only [List.cons_append]
                    exact congrArg (List.cons (layout.frameNode head)) ih
              _ = state.ownedAtoms.map layout.frameNode := by
                rw [InstantiationState.ownedAtoms, hpending]
          rw [hnext]
          induction state.ownedAtoms with
          | nil => rfl
          | cons head tail ih =>
              simp only [List.map_cons, Function.comp_apply]
              exact congrArg (List.cons (restMap (layout.frameNode head))) ih
        · intro node sourceSite hsource
          apply hrestBound
          calc
            layout.plugRaw.nodes (layout.frameNode node) =
                layout.mapFrameNode (state.diagram.val.nodes node) :=
              layout.plugNode_frameNode node
            _ = .atom (layout.frameRegion sourceSite)
                (layout.frameRegion state.bubble) := by
              rw [hsource]
              rfl

theorem instantiateCopies_success_processedAtoms_exact
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (hprocessed : state.processedAtoms = [])
    (hcopy : instantiateCopies comprehension attachments binders payload
      state.pendingAtoms.length state = .ok result) :
    ∃ nodeMap : Fin state.diagram.val.nodeCount →
        Fin result.diagram.val.nodeCount,
      Function.Injective nodeMap ∧
        result.pendingAtoms = [] ∧
        result.processedAtoms = state.pendingAtoms.map nodeMap ∧
        ∀ {node site},
          state.diagram.val.nodes node = .atom site state.bubble →
            ∃ resultSite,
              result.diagram.val.nodes (nodeMap node) =
                .atom resultSite result.bubble := by
  obtain ⟨nodeMap, hinjective, howned, hbound⟩ :=
    instantiateCopies_success_ownedAtoms_map comprehension attachments binders
      payload state.pendingAtoms.length state result hcopy
  have hpending := instantiateCopies_success_pendingAtoms_empty
    comprehension attachments binders payload state result hcopy
  refine ⟨nodeMap, hinjective, hpending, ?_, hbound⟩
  simpa [InstantiationState.ownedAtoms, hprocessed, hpending] using howned

theorem boundAtoms_nodup (input : Checked )
    (bubble : Fin input.val.regionCount) :
    (boundAtoms input bubble).Nodup :=
  filterFin_nodup _

theorem instantiateCopies_success_processedAtoms_nodup
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Checked }
    (state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (hprocessed : state.processedAtoms = [])
    (hpending : state.pendingAtoms.Nodup)
    (hcopy : instantiateCopies comprehension attachments binders payload
      state.pendingAtoms.length state = .ok result) :
    result.processedAtoms.Nodup := by
  obtain ⟨nodeMap, hinjective, _, hexact, _⟩ :=
    instantiateCopies_success_processedAtoms_exact comprehension attachments
      binders payload state result hprocessed hcopy
  rw [hexact]
  have map_nodup : ∀ values : List (Fin state.diagram.val.nodeCount),
      values.Nodup → (values.map nodeMap).Nodup := by
    intro values hvalues
    induction values with
    | nil => simp
    | cons head tail ih =>
        rw [List.nodup_cons] at hvalues
        simp only [List.map_cons]
        rw [List.nodup_cons]
        refine ⟨?_, ih hvalues.2⟩
        intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨source, hsource, heq⟩ := hmem
        have hsourceEq : source = head := hinjective heq
        subst source
        exact hvalues.1 hsource
  exact map_nodup state.pendingAtoms hpending

theorem instantiateCopies_initial_success_exact
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount)
    (hcopy : instantiateCopies comprehension attachments binders payload
      (boundAtoms input bubble).length (initialInstantiationState payload) =
        .ok result) :
    ∃ nodeMap : Fin input.val.nodeCount → Fin result.diagram.val.nodeCount,
      Function.Injective nodeMap ∧
        result.pendingAtoms = [] ∧
        result.processedAtoms = (boundAtoms input bubble).map nodeMap ∧
        result.processedAtoms.Nodup ∧
        ∀ {node site}, input.val.nodes node = .atom site bubble →
          ∃ resultSite,
            result.diagram.val.nodes (nodeMap node) =
              .atom resultSite result.bubble := by
  obtain ⟨nodeMap, hinjective, hpending, hexact, hbound⟩ :=
    instantiateCopies_success_processedAtoms_exact comprehension attachments
      binders payload (initialInstantiationState payload) result rfl hcopy
  have hnodup : result.processedAtoms.Nodup := by
    exact instantiateCopies_success_processedAtoms_nodup comprehension
      attachments binders payload (initialInstantiationState payload) result
      rfl (boundAtoms_nodup input bubble) hcopy
  exact ⟨nodeMap, hinjective, hpending, hexact, hnodup, hbound⟩

def instantiationAtomDomain
    (state : InstantiationState origin p q) :
    SurvivorDomain state.diagram.val.nodeCount :=
  ⟨fun node => decide (node ∉ state.processedAtoms)⟩

@[simp] theorem instantiationAtomDomain_processed
    (state : InstantiationState origin p q)
    {node : Fin state.diagram.val.nodeCount}
    (hnode : node ∈ state.processedAtoms) :
    (instantiationAtomDomain state).survives node = false := by
  simp [instantiationAtomDomain, hnode]

def dropInstantiationAtomsRaw {origin : Checked }
    (state : InstantiationState origin p q) : Concrete.Diagram :=
  let nodes := instantiationAtomDomain state
  { regionCount := state.diagram.val.regionCount
    nodeCount := nodes.count
    wireCount := state.diagram.val.wireCount
    root := state.diagram.val.root
    regions := state.diagram.val.regions
    nodes := fun node => state.diagram.val.nodes (nodes.origin node)
    wires := fun wire =>
      { scope := (state.diagram.val.wires wire).scope
        endpoints := (state.diagram.val.wires wire).endpoints.filterMap
          nodes.reindexEndpoint? }
  }

def finishInstantiation {origin : Checked }
    (state : InstantiationState origin p q) :
    Except Error (OperationReceipt origin) :=
  let droppedRaw := dropInstantiationAtomsRaw state
  let toDroppedProvenance : WireProvenance origin.val droppedRaw :=
    state.provenance.compose
      (WireProvenance.byWireCount state.diagram.val droppedRaw rfl)
  let toDroppedInterface : WireTransport origin.val droppedRaw :=
    state.interface.compose
      (WireTransport.byWireCount state.diagram.val droppedRaw rfl)
  match hraw : vacuousElimRaw? droppedRaw state.bubble with
  | none => .error .nonVacuousBinder
  | some raw =>
      match hcheck : checkWellFormed  raw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (OperationReceipt.ofChecked origin raw
          (toDroppedProvenance.compose (vacuousElimWireProvenance hraw))
          (toDroppedInterface.compose (vacuousElimWireTransport hraw))
          result hcheck)

theorem finishInstantiation_realizes {origin : Checked }
    {state : InstantiationState origin p q}
    {result : OperationReceipt origin}
    (hfinish : finishInstantiation state = .ok result) :
    let droppedRaw := dropInstantiationAtomsRaw state
    let toDroppedProvenance : WireProvenance origin.val droppedRaw :=
      state.provenance.compose
        (WireProvenance.byWireCount state.diagram.val droppedRaw rfl)
    let toDroppedInterface : WireTransport origin.val droppedRaw :=
      state.interface.compose
        (WireTransport.byWireCount state.diagram.val droppedRaw rfl)
    ∃ raw,
      ∃ hraw : vacuousElimRaw? droppedRaw state.bubble = some raw,
        ∃ checked : Checked ,
          ∃ hcheck : checkWellFormed  raw = .ok checked,
            result = OperationReceipt.ofChecked origin raw
                (toDroppedProvenance.compose
                  (vacuousElimWireProvenance hraw))
                (toDroppedInterface.compose
                  (vacuousElimWireTransport hraw))
                checked hcheck ∧
              result.Realizes raw
                (toDroppedProvenance.compose
                  (vacuousElimWireProvenance hraw))
                (toDroppedInterface.compose
                  (vacuousElimWireTransport hraw)) := by
  dsimp only
  unfold finishInstantiation at hfinish
  dsimp only at hfinish
  split at hfinish <;> try contradiction
  rename_i raw hraw
  split at hfinish <;> try contradiction
  rename_i checked hcheck
  cases hfinish
  exact ⟨raw, hraw, checked, hcheck, rfl,
    OperationReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

def applyComprehensionInstantiate (orientation : Orientation)
    (input : Checked )
    (bubble : Fin input.val.regionCount)
    (comprehension : CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders) : Except Error (OperationReceipt input) :=
  if spawnPolarity orientation (concreteCutDepth input.val bubble) then
    let initial := initialInstantiationState payload
    match instantiateCopies comprehension attachments binders payload
        initial.pendingAtoms.length initial with
    | .error error => .error error
    | .ok copied => finishInstantiation copied
  else
    .error .wrongPolarity

theorem applyComprehensionInstantiate_success
    (happly : applyComprehensionInstantiate orientation input bubble
      comprehension attachments binders payload = .ok result) :
    spawnPolarity orientation (concreteCutDepth input.val bubble) ∧
      ∃ copied : InstantiationState input attachments.length
          payload.binderSpine.proxyCount,
        let initial := initialInstantiationState payload
        instantiateCopies comprehension attachments binders payload
            initial.pendingAtoms.length initial = .ok copied ∧
          finishInstantiation copied = .ok result := by
  have hpolarity : spawnPolarity orientation
      (concreteCutDepth input.val bubble) := by
    by_cases h : spawnPolarity orientation
        (concreteCutDepth input.val bubble)
    · exact h
    · simp [applyComprehensionInstantiate, h] at happly
  refine ⟨hpolarity, ?_⟩
  unfold applyComprehensionInstantiate at happly
  rw [if_pos hpolarity] at happly
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i copied hcopied
  exact ⟨copied, hcopied, happly⟩

theorem applyComprehensionInstantiate_realizes {orientation : Orientation}
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {result : OperationReceipt input}
    (happly : applyComprehensionInstantiate orientation input bubble
      comprehension attachments binders payload = .ok result) :
    spawnPolarity orientation (concreteCutDepth input.val bubble) ∧
      let initial := initialInstantiationState payload
      ∃ copied : InstantiationState input attachments.length
          payload.binderSpine.proxyCount,
        instantiateCopies comprehension attachments binders payload
            initial.pendingAtoms.length initial = .ok copied ∧
          let droppedRaw := dropInstantiationAtomsRaw copied
          let toDroppedProvenance : WireProvenance input.val droppedRaw :=
            copied.provenance.compose
              (WireProvenance.byWireCount copied.diagram.val droppedRaw rfl)
          let toDroppedInterface : WireTransport input.val droppedRaw :=
            copied.interface.compose
              (WireTransport.byWireCount copied.diagram.val droppedRaw rfl)
          ∃ raw,
            ∃ hraw : vacuousElimRaw? droppedRaw copied.bubble = some raw,
              ∃ checked : Checked ,
                ∃ hcheck : checkWellFormed  raw = .ok checked,
                  result = OperationReceipt.ofChecked input raw
                      (toDroppedProvenance.compose
                        (vacuousElimWireProvenance hraw))
                      (toDroppedInterface.compose
                        (vacuousElimWireTransport hraw))
                      checked hcheck ∧
                    result.Realizes raw
                      (toDroppedProvenance.compose
                        (vacuousElimWireProvenance hraw))
                      (toDroppedInterface.compose
                        (vacuousElimWireTransport hraw)) := by
  have hpolarity : spawnPolarity orientation
      (concreteCutDepth input.val bubble) := by
    by_cases h : spawnPolarity orientation
        (concreteCutDepth input.val bubble)
    · exact h
    · simp [applyComprehensionInstantiate, h] at happly
  refine ⟨hpolarity, ?_⟩
  unfold applyComprehensionInstantiate at happly
  rw [if_pos hpolarity] at happly
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i copied hcopied
  exact ⟨copied, hcopied, finishInstantiation_realizes happly⟩


/-- Full second-order existential introduction; the witness is an arbitrary relation. -/
theorem comprehension_witness
    (relation : Relation D arity) (body : Relation D arity → Prop) :
    body relation → ∃ candidate : Relation D arity, body candidate := by
  intro hbody
  exact ⟨relation, hbody⟩

/-- The diagonal witness denotes exactly capture-avoiding boundary substitution. -/
theorem diagonalize_denotation
    {input : Checked }
    {comprehension : CheckedOpen }
    {occurrence : OperationAbstractionOccurrence input}
    (witness : OperationAbstractionWitness input comprehension occurrence)
    (model : Model)
    (env : Fin occurrence.selection.touchingWires.length → model.Carrier) :
    witness.diagonal.denote model
        ((env ∘ Fin.cast witness.diagonal_externalClasses) ∘
          witness.diagonal.elaborate.boundary) ↔
      comprehension.denote model  (env ∘ witness.assignment.args) := by
  change denoteOpen model  witness.diagonal.elaborate
      ((env ∘ Fin.cast witness.diagonal_externalClasses) ∘
        witness.diagonal.elaborate.boundary) ↔
    denoteOpen model  comprehension.elaborate
      (env ∘ witness.assignment.args)
  let diagonalEnv := env ∘ Fin.cast witness.diagonal_externalClasses
  have hdiagonal :
      denoteOpen model  witness.diagonal.elaborate
          (diagonalEnv ∘ witness.diagonal.elaborate.boundary) ↔
        denoteRegion (relCtx := []) model  diagonalEnv PUnit.unit
          witness.diagonal.elaborate.body := by
    have h := (OpenDiagram.denote_substituteBoundary
      witness.diagonal.elaborate
      witness.diagonal.elaborate.identityBoundaryAssignment model
      diagonalEnv).symm
    rw [witness.diagonal.elaborate.substituteBoundary_id] at h
    simpa [OpenDiagram.identityBoundaryAssignment] using h
  rw [hdiagonal]
  have hrename := denoteRegion_renameWires
    (relCtx := []) model  (Fin.cast witness.diagonal_externalClasses)
    env PUnit.unit witness.diagonal.elaborate.body
  change denoteRegion (relCtx := []) model  diagonalEnv PUnit.unit
      witness.diagonal.elaborate.body ↔ _
  rw [← hrename]
  rw [← Region.castWiresEq_eq_renameWires]
  rw [witness.diagonal_body_eq]
  exact OpenDiagram.denote_substituteBoundary
    comprehension.elaborate witness.assignment model  env

/-- Positive abstraction is existential generalization. -/
theorem comprehensionAbstract_sound
    (relation : Relation D arity) (body : Relation D arity → Prop) :
    body relation → ∃ candidate : Relation D arity, body candidate :=
  comprehension_witness relation body

/-- At negative polarity, the same local implication is consumed contravariantly. -/
theorem comprehensionInstantiate_sound
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (specialized quantified : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (negative : ctx.cutDepth % 2 = 1)
    (hlocal : ∀ holeEnv holeRelEnv,
      denoteRegion model  holeEnv holeRelEnv specialized →
        denoteRegion model  holeEnv holeRelEnv quantified) :
    denoteRegion model  env rels (ctx.fill quantified) →
      denoteRegion model  env rels (ctx.fill specialized) :=
  context_anti model  env rels negative hlocal

/-- At positive polarity, existential generalization is covariant. -/
theorem comprehensionAbstract_context_sound
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (specialized quantified : Region  holeWires holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (positive : ctx.cutDepth % 2 = 0)
    (hlocal : ∀ holeEnv holeRelEnv,
      denoteRegion model  holeEnv holeRelEnv specialized →
        denoteRegion model  holeEnv holeRelEnv quantified) :
    denoteRegion model  env rels (ctx.fill specialized) →
      denoteRegion model  env rels (ctx.fill quantified) :=
  context_mono model  env rels positive hlocal

end VisualProof.Concrete
