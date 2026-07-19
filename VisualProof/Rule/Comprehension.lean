import VisualProof.Rule.Equational

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

def abstractionRegions (occurrences : List (AbstractionOccurrence input)) :
    List (Fin input.val.regionCount) :=
  occurrences.flatMap fun occurrence => occurrence.selection.selectedRegions

def abstractionNodes (occurrences : List (AbstractionOccurrence input)) :
    List (Fin input.val.nodeCount) :=
  occurrences.flatMap fun occurrence => occurrence.selection.selectedNodes

def abstractionWires (occurrences : List (AbstractionOccurrence input)) :
    List (Fin input.val.wireCount) :=
  occurrences.flatMap fun occurrence => occurrence.selection.internalWires

structure AbstractionDomains (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input)) where
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
def abstractionDomains (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input)) :
    AbstractionDomains input occurrences := {}

def abstractRegion? (input : CheckedDiagram signature)
    (wrap : CheckedSelection input.val)
    (occurrences : List (AbstractionOccurrence input))
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

def abstractNode? (input : CheckedDiagram signature)
    (wrap : CheckedSelection input.val)
    (occurrences : List (AbstractionOccurrence input))
    (domains : AbstractionDomains input occurrences)
    (bubble : Fin (domains.regions.count + 1))
    (original : Fin input.val.nodeCount) :
    Option (CNode (domains.regions.count + 1)) :=
  let owner? (owner : Fin input.val.regionCount) :=
    if original ∈ wrap.val.directNodes then some bubble
    else (domains.regions.index? owner).map Fin.castSucc
  match input.val.nodes original with
  | .term owner freePorts term =>
      (owner? owner).map fun mapped => .term mapped freePorts term
  | .atom owner binder => do
      let mappedOwner ← owner? owner
      let mappedBinder ← domains.regions.index? binder
      pure (.atom mappedOwner mappedBinder.castSucc)
  | .named owner definition arity =>
      (owner? owner).map fun mapped => .named mapped definition arity

def abstractFrameEndpoints
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (domains : AbstractionDomains input occurrences)
    (wire : domains.wires.Carrier) :
    List (CEndpoint (domains.nodes.count + occurrences.length)) :=
  (input.val.wires (domains.wires.origin wire)).endpoints.filterMap fun endpoint =>
    (domains.nodes.reindexEndpoint? endpoint).map fun mapped =>
      { node := mapped.node.castAdd occurrences.length, port := mapped.port }

def abstractAtomEndpoints
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
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
    (input : CheckedDiagram signature)
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpenDiagram signature)
    (occurrences : List (AbstractionOccurrence input)) :
    Option { raw : ConcreteDiagram //
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
    (input : CheckedDiagram signature)
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpenDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (raw : ConcreteDiagram) where
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

private def comprehensionAbstractWireProvenance
    (input : CheckedDiagram signature)
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpenDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (raw : ConcreteDiagram)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw) : WireProvenance input.val raw :=
  let domains : AbstractionDomains input occurrences := {}
  WireProvenance.survivors input.val raw domains.wires (by
    rw [Option.map_eq_some_iff] at hraw
    obtain ⟨witness, _, equality⟩ := hraw
    subst raw
    exact witness.property)

private def comprehensionAbstractInterfaceTransport
    (input : CheckedDiagram signature)
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpenDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (raw : ConcreteDiagram)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw) : InterfaceTransport input.val raw :=
  let domains : AbstractionDomains input occurrences := {}
  InterfaceTransport.survivors input.val raw domains.wires (by
    rw [Option.map_eq_some_iff] at hraw
    obtain ⟨witness, _, equality⟩ := hraw
    subst raw
    exact witness.property)

def applyComprehensionAbstract (orientation : Orientation)
    (input : CheckedDiagram signature)
    (wrap : CheckedSelection input.val)
    (comprehension : CheckedOpenDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (_payload : ComprehensionAbstractPayload input wrap comprehension occurrences) :
    Except StepError (StepReceipt input) :=
  if erasurePolarity orientation
      (concreteCutDepth input.val wrap.val.anchor) then
    match hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
        Subtype.val with
    | none => .error .operationRejected
    | some raw =>
        match hcheck : checkWellFormed signature raw with
        | .error error => .error (.resultNotWellFormed error)
        | .ok result => .ok (StepReceipt.ofChecked input raw
            (comprehensionAbstractWireProvenance input wrap comprehension
              occurrences raw hraw)
            (comprehensionAbstractInterfaceTransport input wrap comprehension
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
            (comprehensionAbstractInterfaceTransport input wrap comprehension
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
  exact ⟨raw, hraw, StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

structure InstantiationState {signature : List Nat}
    (origin : CheckedDiagram signature)
    (parameterCount proxyCount : Nat) where
  diagram : CheckedDiagram signature
  provenance : WireProvenance origin.val diagram.val
  interface : InterfaceTransport origin.val diagram.val
  bubble : Fin diagram.val.regionCount
  parameters : Fin parameterCount → Fin diagram.val.wireCount
  binderTargets : Fin proxyCount → Fin diagram.val.regionCount
  pendingAtoms : List (Fin diagram.val.nodeCount)
  processedAtoms : List (Fin diagram.val.nodeCount)

def InstantiationState.ownedAtoms
    (state : InstantiationState origin parameterCount proxyCount) :
    List (Fin state.diagram.val.nodeCount) :=
  state.processedAtoms ++ state.pendingAtoms

private def comprehensionSpliceError : Splice.Input.Error → StepError
  | .attachmentNotVisible => .boundaryMismatch
  | .duplicateBinderTarget => .binderEscape
  | .binderKindOrArityMismatch => .binderKindOrArityMismatch
  | .binderDoesNotEncloseSite => .binderDoesNotEnclose
  | .resultNotWellFormed error => .resultNotWellFormed error

def boundAtoms (input : CheckedDiagram signature)
    (bubble : Fin input.val.regionCount) : List (Fin input.val.nodeCount) :=
  filterFin fun node =>
    match input.val.nodes node with
    | .atom _ binder => decide (binder = bubble)
    | _ => false

theorem mem_boundAtoms_iff (input : CheckedDiagram signature)
    (bubble : Fin input.val.regionCount)
    (node : Fin input.val.nodeCount) :
    node ∈ boundAtoms input bubble ↔
      ∃ site, input.val.nodes node = .atom site bubble := by
  rw [boundAtoms, mem_filterFin]
  cases hnode : input.val.nodes node with
  | term region freePorts term => simp
  | atom site binder =>
      simp only [decide_eq_true_eq]
      constructor
      · intro heq
        subst binder
        exact ⟨site, rfl⟩
      · rintro ⟨candidate, heq⟩
        cases heq
        rfl
  | named region definition arity => simp

def initialInstantiationState
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders) :
    InstantiationState input attachments.length payload.binderSpine.proxyCount := {
  diagram := input
  provenance := WireProvenance.identity input.val
  interface := InterfaceTransport.identity input.val
  bubble := bubble
  parameters := attachments.get
  binderTargets := payload.binderTargets
  pendingAtoms := boundAtoms input bubble
  processedAtoms := []
}

/-- Repackage the source comprehension certificate for the checked
alias-materialized graph used by the executor.  Regions and the designated
binder spine are unchanged; only boundary wire identities and terminal-body
identity nodes are added. -/
def materializedInstantiationPayload
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (certificate : Splice.AliasMaterialization.Certificate comprehension
      payload.binderSpine) :
    ComprehensionInstantiatePayload input bubble certificate.result attachments
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
    ConcreteElaboration.endpointOwner? state.diagram.val
      { node := node, port := .arg index }

def instantiateSpliceInput {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount) :
    Splice.Input signature where
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
def advanceInstantiationState {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
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
  let nextDiagram : CheckedDiagram signature :=
    ⟨layout.plugRaw,
      Splice.Input.PlugLayout.plugRaw_wellFormed signature spliceInput layout
        hadmissible⟩
  {
    diagram := nextDiagram
    provenance := state.provenance.compose
      (spliceFrameWireProvenance spliceInput)
    interface := state.interface.compose
      (spliceFrameInterfaceTransport spliceInput)
    bubble := layout.frameRegion state.bubble
    parameters := fun index =>
      layout.frameWire (spliceInput.quotientWire (state.parameters index))
    binderTargets := fun index =>
      layout.frameRegion (state.binderTargets index)
    pendingAtoms := tail.map layout.frameNode
    processedAtoms := state.processedAtoms.map layout.frameNode ++
      [layout.frameNode atom]
  }

def instantiateCopies {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature} :
    Nat → InstantiationState origin attachments.length
      payload.binderSpine.proxyCount →
      Except StepError (InstantiationState origin attachments.length
        payload.binderSpine.proxyCount)
  | 0, state =>
      if state.pendingAtoms.isEmpty then .ok state else .error .operationRejected
  | fuel + 1, state =>
      match state.pendingAtoms with
      | [] => .ok state
      | atom :: tail =>
          match state.diagram.val.nodes atom with
          | .term .. | .named .. => .error .operationRejected
          | .atom site candidate =>
              if candidate = state.bubble then
                match instantiateArguments? state atom payload.arity with
                | none => .error .boundaryMismatch
                | some arguments =>
                    let spliceInput := instantiateSpliceInput
                      comprehension attachments binders payload state site arguments
                    match hinput : Splice.Input.checkInput spliceInput with
                    | .error error => .error (comprehensionSpliceError error)
                    | .ok _ =>
                        have hadmissible : spliceInput.Admissible :=
                          (Splice.Input.checkInput_sound hinput).2
                        let next := advanceInstantiationState comprehension
                          attachments binders payload state atom tail site
                          arguments hadmissible
                        instantiateCopies comprehension attachments binders payload
                          fuel next
              else
                .error .operationRejected

theorem instantiateCopies_success_pendingAtoms_empty
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
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
          rename_i checkedInput hinput
          apply ih _ _ _ hcopy
          simpa [advanceInstantiationState] using htail

/-- A successful copy run transports the complete owned-atom list through one
composed total injective node map.  Unlike receipt provenance, this map retains
nodes through every splice and therefore records the exact removal ownership. -/
theorem instantiateCopies_success_ownedAtoms_map
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
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
        rename_i checkedInput hinput
        let spliceInput := instantiateSpliceInput comprehension attachments
          binders payload state site arguments
        have hadmissible : spliceInput.Admissible :=
          (Splice.Input.checkInput_sound hinput).2
        let layout := spliceInput.plugLayout
        let nextDiagram : CheckedDiagram signature :=
          ⟨layout.plugRaw,
            Splice.Input.PlugLayout.plugRaw_wellFormed
              signature spliceInput layout hadmissible⟩
        let next : InstantiationState origin attachments.length
            payload.binderSpine.proxyCount := {
          diagram := nextDiagram
          provenance := state.provenance.compose
            (spliceFrameWireProvenance spliceInput)
          interface := state.interface.compose
            (spliceFrameInterfaceTransport spliceInput)
          bubble := layout.frameRegion state.bubble
          parameters := fun index =>
            layout.frameWire (spliceInput.quotientWire (state.parameters index))
          binderTargets := fun index =>
            layout.frameRegion (state.binderTargets index)
          pendingAtoms := tail.map layout.frameNode
          processedAtoms := state.processedAtoms.map layout.frameNode ++
            [layout.frameNode atom]
        }
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
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
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

theorem boundAtoms_nodup (input : CheckedDiagram signature)
    (bubble : Fin input.val.regionCount) :
    (boundAtoms input bubble).Nodup :=
  filterFin_nodup _

theorem instantiateCopies_success_processedAtoms_nodup
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
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
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
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

def dropInstantiationAtomsRaw {signature : List Nat}
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin p q) : ConcreteDiagram :=
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

def finishInstantiation {signature : List Nat}
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin p q) :
    Except StepError (StepReceipt origin) :=
  let droppedRaw := dropInstantiationAtomsRaw state
  let toDroppedProvenance : WireProvenance origin.val droppedRaw :=
    state.provenance.compose
      (WireProvenance.byWireCount state.diagram.val droppedRaw rfl)
  let toDroppedInterface : InterfaceTransport origin.val droppedRaw :=
    state.interface.compose
      (InterfaceTransport.byWireCount state.diagram.val droppedRaw rfl)
  match hraw : vacuousElimRaw? droppedRaw state.bubble with
  | none => .error .nonVacuousBinder
  | some raw =>
      match hcheck : checkWellFormed signature raw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (StepReceipt.ofChecked origin raw
          (toDroppedProvenance.compose (vacuousElimWireProvenance hraw))
          (toDroppedInterface.compose (vacuousElimInterfaceTransport hraw))
          result hcheck)

theorem finishInstantiation_realizes {signature : List Nat}
    {origin : CheckedDiagram signature}
    {state : InstantiationState origin p q}
    {result : StepReceipt origin}
    (hfinish : finishInstantiation state = .ok result) :
    let droppedRaw := dropInstantiationAtomsRaw state
    let toDroppedProvenance : WireProvenance origin.val droppedRaw :=
      state.provenance.compose
        (WireProvenance.byWireCount state.diagram.val droppedRaw rfl)
    let toDroppedInterface : InterfaceTransport origin.val droppedRaw :=
      state.interface.compose
        (InterfaceTransport.byWireCount state.diagram.val droppedRaw rfl)
    ∃ raw,
      ∃ hraw : vacuousElimRaw? droppedRaw state.bubble = some raw,
        ∃ checked : CheckedDiagram signature,
          ∃ hcheck : checkWellFormed signature raw = .ok checked,
            result = StepReceipt.ofChecked origin raw
                (toDroppedProvenance.compose
                  (vacuousElimWireProvenance hraw))
                (toDroppedInterface.compose
                  (vacuousElimInterfaceTransport hraw))
                checked hcheck ∧
              result.Realizes raw
                (toDroppedProvenance.compose
                  (vacuousElimWireProvenance hraw))
                (toDroppedInterface.compose
                  (vacuousElimInterfaceTransport hraw)) := by
  dsimp only
  unfold finishInstantiation at hfinish
  dsimp only at hfinish
  split at hfinish <;> try contradiction
  rename_i raw hraw
  split at hfinish <;> try contradiction
  rename_i checked hcheck
  cases hfinish
  exact ⟨raw, hraw, checked, hcheck, rfl,
    StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

def applyComprehensionInstantiate (orientation : Orientation)
    (input : CheckedDiagram signature)
    (bubble : Fin input.val.regionCount)
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders) : Except StepError (StepReceipt input) :=
  if spawnPolarity orientation (concreteCutDepth input.val bubble) then
    match Splice.AliasMaterialization.check comprehension payload.binderSpine
        payload.terminalBody with
    | .error error => .error (.resultNotWellFormed error)
    | .ok materialization =>
        let operational := materialization.result
        let operationalPayload := materializedInstantiationPayload payload
          materialization
        let initial := initialInstantiationState operationalPayload
        match instantiateCopies operational attachments binders
            operationalPayload initial.pendingAtoms.length initial with
        | .error error => .error error
        | .ok copied => finishInstantiation copied
  else
    .error .wrongPolarity

theorem applyComprehensionInstantiate_success
    (happly : applyComprehensionInstantiate orientation input bubble
      comprehension attachments binders payload = .ok result) :
    spawnPolarity orientation (concreteCutDepth input.val bubble) ∧
      ∃ materialization : Splice.AliasMaterialization.Certificate comprehension
          payload.binderSpine,
        Splice.AliasMaterialization.check comprehension payload.binderSpine
            payload.terminalBody = .ok materialization ∧
          let operational := materialization.result
          let operationalPayload := materializedInstantiationPayload payload
            materialization
          ∃ copied : InstantiationState input attachments.length
              operationalPayload.binderSpine.proxyCount,
            let initial := initialInstantiationState operationalPayload
            instantiateCopies operational attachments binders
                operationalPayload initial.pendingAtoms.length initial =
                  .ok copied ∧
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
  rename_i materialization hmaterialization
  split at happly <;> try contradiction
  rename_i copied hcopied
  exact ⟨materialization, hmaterialization, copied, hcopied, happly⟩

theorem applyComprehensionInstantiate_realizes {signature : List Nat}
    {orientation : Orientation}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {result : StepReceipt input}
    (happly : applyComprehensionInstantiate orientation input bubble
      comprehension attachments binders payload = .ok result) :
    spawnPolarity orientation (concreteCutDepth input.val bubble) ∧
      ∃ materialization : Splice.AliasMaterialization.Certificate comprehension
          payload.binderSpine,
        Splice.AliasMaterialization.check comprehension payload.binderSpine
            payload.terminalBody = .ok materialization ∧
          let operational := materialization.result
          let operationalPayload := materializedInstantiationPayload payload
            materialization
          let initial := initialInstantiationState operationalPayload
          ∃ copied : InstantiationState input attachments.length
              operationalPayload.binderSpine.proxyCount,
            instantiateCopies operational attachments binders
                operationalPayload initial.pendingAtoms.length initial =
                  .ok copied ∧
              let droppedRaw := dropInstantiationAtomsRaw copied
              let toDroppedProvenance : WireProvenance input.val droppedRaw :=
                copied.provenance.compose
                  (WireProvenance.byWireCount copied.diagram.val droppedRaw rfl)
              let toDroppedInterface : InterfaceTransport input.val droppedRaw :=
                copied.interface.compose
                  (InterfaceTransport.byWireCount copied.diagram.val droppedRaw rfl)
              ∃ raw,
                ∃ hraw : vacuousElimRaw? droppedRaw copied.bubble = some raw,
                  ∃ checked : CheckedDiagram signature,
                    ∃ hcheck : checkWellFormed signature raw = .ok checked,
                      result = StepReceipt.ofChecked input raw
                          (toDroppedProvenance.compose
                            (vacuousElimWireProvenance hraw))
                          (toDroppedInterface.compose
                            (vacuousElimInterfaceTransport hraw))
                          checked hcheck ∧
                        result.Realizes raw
                          (toDroppedProvenance.compose
                            (vacuousElimWireProvenance hraw))
                          (toDroppedInterface.compose
                            (vacuousElimInterfaceTransport hraw)) := by
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
  rename_i materialization hmaterialization
  split at happly <;> try contradiction
  rename_i copied hcopied
  exact ⟨materialization, hmaterialization, copied, hcopied,
    finishInstantiation_realizes happly⟩

namespace ComprehensionInstantiationExamples

def nonemptyHostRaw : ConcreteDiagram where
  regionCount := 3
  nodeCount := 1
  wireCount := 0
  root := 0
  regions := fun region =>
    if region = 0 then .sheet
    else if region = 1 then .cut 0
    else .bubble 1 0
  nodes := fun _ => .atom 2 2
  wires := nofun

theorem nonemptyHostRaw_check :
    ∃ checked, checkWellFormed [] nonemptyHostRaw = .ok checked ∧
      checked.val = nonemptyHostRaw := by
  refine ⟨_, rfl, rfl⟩

def nonemptyHost : CheckedDiagram [] :=
  ⟨nonemptyHostRaw, checkWellFormed_iff.mp nonemptyHostRaw_check⟩

def selectedBubble : Fin nonemptyHost.val.regionCount :=
  ⟨2, by decide⟩

def emptyComprehensionRaw : OpenConcreteDiagram where
  diagram := {
    regionCount := 1
    nodeCount := 0
    wireCount := 0
    root := 0
    regions := fun _ => .sheet
    nodes := nofun
    wires := nofun
  }
  boundary := []

theorem emptyComprehensionDiagram_check :
    ∃ checked,
      checkWellFormed [] emptyComprehensionRaw.diagram = .ok checked ∧
        checked.val = emptyComprehensionRaw.diagram := by
  refine ⟨_, rfl, rfl⟩

theorem emptyComprehensionRaw_wellFormed :
    emptyComprehensionRaw.WellFormed [] where
  diagram_well_formed := checkWellFormed_iff.mp emptyComprehensionDiagram_check
  boundary_is_root_scoped := by
    intro wire hwire
    exact Fin.elim0 wire

def emptyComprehension : CheckedOpenDiagram [] :=
  ⟨emptyComprehensionRaw, emptyComprehensionRaw_wellFormed⟩

def payload : ComprehensionInstantiatePayload nonemptyHost selectedBubble
    emptyComprehension [] [] where
  parent := ⟨1, by decide⟩
  arity := 0
  bubble_eq := by native_decide
  boundarySplit := rfl
  parameterScopesProper := nofun
  binderSpine := emptyBinderSpine emptyComprehension
  terminalBody := emptyTerminalBody emptyComprehension
  binderTargets := nofun
  binderPairsExact := rfl
  binderTargetsProper := nofun

/-- The rebuilt loop executes a genuinely nonempty replacement, removes its
processed atom, and dissolves the now-vacuous relation bubble. -/
theorem nonempty_instantiation_succeeds :
    ∃ result, applyComprehensionInstantiate .forward nonemptyHost
      selectedBubble emptyComprehension [] [] payload = .ok result := by
  refine ⟨_, rfl⟩

end ComprehensionInstantiationExamples

/-- Full second-order existential introduction; the witness is an arbitrary relation. -/
theorem comprehension_witness
    (relation : Relation D arity) (body : Relation D arity → Prop) :
    body relation → ∃ candidate : Relation D arity, body candidate := by
  intro hbody
  exact ⟨relation, hbody⟩

/-- The diagonal witness denotes exactly capture-avoiding boundary substitution. -/
theorem diagonalize_denotation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {comprehension : CheckedOpenDiagram signature}
    {occurrence : AbstractionOccurrence input}
    (witness : AbstractionWitness input comprehension occurrence)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin occurrence.selection.touchingWires.length → model.Carrier) :
    witness.diagonal.denote model named
        ((env ∘ Fin.cast witness.diagonal_externalClasses) ∘
          witness.diagonal.elaborate.boundary) ↔
      comprehension.denote model named (env ∘ witness.assignment.args) := by
  change denoteOpen model named witness.diagonal.elaborate
      ((env ∘ Fin.cast witness.diagonal_externalClasses) ∘
        witness.diagonal.elaborate.boundary) ↔
    denoteOpen model named comprehension.elaborate
      (env ∘ witness.assignment.args)
  let diagonalEnv := env ∘ Fin.cast witness.diagonal_externalClasses
  have hdiagonal :
      denoteOpen model named witness.diagonal.elaborate
          (diagonalEnv ∘ witness.diagonal.elaborate.boundary) ↔
        denoteRegion (relCtx := []) model named diagonalEnv PUnit.unit
          witness.diagonal.elaborate.body := by
    have h := (OpenDiagram.denote_substituteBoundary
      witness.diagonal.elaborate
      witness.diagonal.elaborate.identityBoundaryAssignment model named
      diagonalEnv).symm
    rw [witness.diagonal.elaborate.substituteBoundary_id] at h
    simpa [OpenDiagram.identityBoundaryAssignment] using h
  rw [hdiagonal]
  have hrename := denoteRegion_renameWires
    (relCtx := []) model named (Fin.cast witness.diagonal_externalClasses)
    env PUnit.unit witness.diagonal.elaborate.body
  change denoteRegion (relCtx := []) model named diagonalEnv PUnit.unit
      witness.diagonal.elaborate.body ↔ _
  rw [← hrename]
  rw [← Region.castWiresEq_eq_renameWires]
  rw [witness.diagonal_body_eq]
  exact OpenDiagram.denote_substituteBoundary
    comprehension.elaborate witness.assignment model named env

/-- Positive abstraction is existential generalization. -/
theorem comprehensionAbstract_sound
    (relation : Relation D arity) (body : Relation D arity → Prop) :
    body relation → ∃ candidate : Relation D arity, body candidate :=
  comprehension_witness relation body

/-- At negative polarity, the same local implication is consumed contravariantly. -/
theorem comprehensionInstantiate_sound
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (specialized quantified : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (negative : ctx.cutDepth % 2 = 1)
    (hlocal : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv specialized →
        denoteRegion model named holeEnv holeRelEnv quantified) :
    denoteRegion model named env rels (ctx.fill quantified) →
      denoteRegion model named env rels (ctx.fill specialized) :=
  context_anti model named env rels negative hlocal

/-- At positive polarity, existential generalization is covariant. -/
theorem comprehensionAbstract_context_sound
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (specialized quantified : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (positive : ctx.cutDepth % 2 = 0)
    (hlocal : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv specialized →
        denoteRegion model named holeEnv holeRelEnv quantified) :
    denoteRegion model named env rels (ctx.fill specialized) →
      denoteRegion model named env rels (ctx.fill quantified) :=
  context_mono model named env rels positive hlocal

end VisualProof.Rule
