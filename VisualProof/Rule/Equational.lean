import VisualProof.Rule.Structural

namespace VisualProof.Rule

open VisualProof
open Lambda
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- Two injective finite port interfaces into one covered carrier have a
single environment exactly when values agree at shared images.  This is the
semantic bridge used by conversion, congruence, and head stripping; coverage
avoids assuming that the model carrier is inhabited for unused common slots. -/
theorem exists_commonPort_environment
    {leftPorts rightPorts commonPorts : Nat}
    (leftPort : Fin leftPorts → Fin commonPorts)
    (rightPort : Fin rightPorts → Fin commonPorts)
    (leftInjective : Function.Injective leftPort)
    (rightInjective : Function.Injective rightPort)
    (covered : ∀ common,
      (∃ left, leftPort left = common) ∨
        (∃ right, rightPort right = common))
    (leftValue : Fin leftPorts → D)
    (rightValue : Fin rightPorts → D)
    (aligned : ∀ left right,
      leftPort left = rightPort right → leftValue left = rightValue right) :
    ∃ environment : Fin commonPorts → D,
      environment ∘ leftPort = leftValue ∧
        environment ∘ rightPort = rightValue := by
  classical
  let environment : Fin commonPorts → D := fun common =>
    if hleft : ∃ left, leftPort left = common then
      leftValue hleft.choose
    else
      rightValue ((covered common).resolve_left hleft).choose
  refine ⟨environment, funext fun left => ?_, funext fun right => ?_⟩
  · simp only [Function.comp_apply, environment]
    split
    · rename_i hleft
      exact congrArg leftValue (leftInjective hleft.choose_spec)
    · rename_i hnone
      exact False.elim (hnone ⟨left, rfl⟩)
  · simp only [Function.comp_apply, environment]
    split
    · rename_i hleft
      exact aligned hleft.choose right hleft.choose_spec
    · rename_i hnone
      let hright := (covered (rightPort right)).resolve_left hnone
      have heq : hright.choose = right :=
        rightInjective hright.choose_spec
      simp [heq]

theorem LambdaModel.eval_compact (model : LambdaModel)
    (term : Term 0 (Fin ports))
    (environment : Fin ports → model.Carrier) :
    model.eval term.compact (environment ∘ term.freeSupport.get) =
      model.eval term environment := by
  rw [← model.eval_mapFree]
  exact congrArg (fun candidate => model.eval candidate environment)
    term.compact_reconstruct

private def findAttachment? (attachments :
    List (Fin ports × Fin wires)) (port : Fin ports) : Option (Fin wires) :=
  match attachments with
  | [] => none
  | (candidate, wire) :: rest =>
      if candidate = port then some wire else findAttachment? rest port

private theorem findAttachment?_sound
    {attachments : List (Fin ports × Fin wires)} {port : Fin ports}
    {wire : Fin wires}
    (hfind : findAttachment? attachments port = some wire) :
    (port, wire) ∈ attachments := by
  induction attachments with
  | nil => simp [findAttachment?] at hfind
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateWire⟩
      simp only [findAttachment?] at hfind
      split at hfind
      · rename_i heq
        cases hfind
        simp [heq]
      · exact List.mem_cons_of_mem _ (ih hfind)

private theorem findAttachment?_complete
    {attachments : List (Fin ports × Fin wires)} {port : Fin ports}
    {wire : Fin wires}
    (hmem : (port, wire) ∈ attachments) :
    ∃ found, findAttachment? attachments port = some found := by
  induction attachments with
  | nil => simp at hmem
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateWire⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hrest
      · cases heq
        exact ⟨wire, by simp [findAttachment?]⟩
      · obtain ⟨found, hfound⟩ := ih hrest
        by_cases heq : candidate = port
        · exact ⟨candidateWire, by simp [findAttachment?, heq]⟩
        · exact ⟨found, by simp [findAttachment?, heq, hfound]⟩

def ConversionPayload.findOldPort?
    (payload : ConversionPayload input node)
    (port : Fin payload.newFreePorts) : Option (Fin payload.oldFreePorts) :=
  (filterFin fun old => decide (payload.oldPort old = payload.newPort port)).head?

theorem ConversionPayload.findOldPort?_sound
    (payload : ConversionPayload input node)
    {port : Fin payload.newFreePorts} {old : Fin payload.oldFreePorts}
    (hfind : payload.findOldPort? port = some old) :
    payload.oldPort old = payload.newPort port := by
  unfold ConversionPayload.findOldPort? at hfind
  generalize hs : filterFin
      (fun candidate => decide
        (payload.oldPort candidate = payload.newPort port)) = owners at hfind
  cases owners with
  | nil => simp at hfind
  | cons head tail =>
      simp at hfind
      subst old
      have hmem : head ∈ filterFin
          (fun candidate => decide
            (payload.oldPort candidate = payload.newPort port)) := by
        rw [hs]
        simp
      simpa using hmem

theorem ConversionPayload.findOldPort?_complete
    (payload : ConversionPayload input node)
    {port : Fin payload.newFreePorts} {old : Fin payload.oldFreePorts}
    (heq : payload.oldPort old = payload.newPort port) :
    ∃ found, payload.findOldPort? port = some found := by
  have hmem : old ∈ filterFin
      (fun candidate => decide
        (payload.oldPort candidate = payload.newPort port)) := by
    simpa using heq
  unfold ConversionPayload.findOldPort?
  generalize hs : filterFin
      (fun candidate => decide
        (payload.oldPort candidate = payload.newPort port)) = owners at hmem
  cases owners with
  | nil => simp at hmem
  | cons head tail => exact ⟨head, rfl⟩

private theorem ConversionPayload.oldOwner_isSome
    (payload : ConversionPayload input node)
    (port : Fin payload.oldFreePorts) :
    (Diagram.ConcreteElaboration.endpointOwner? input.val
      { node := node, port := .free port }).isSome = true := by
  have hcovered := input.property.required_ports_are_covered node
  rw [payload.node_eq] at hcovered
  obtain ⟨wire, hwire⟩ := hcovered.2 port
  exact Option.isSome_iff_exists.mpr
    (Diagram.ConcreteElaboration.endpointOwner?_complete hwire)

def ConversionPayload.oldWire
    (payload : ConversionPayload input node)
    (port : Fin payload.oldFreePorts) : Fin input.val.wireCount :=
  (Diagram.ConcreteElaboration.endpointOwner? input.val
    { node := node, port := .free port }).get
      (payload.oldOwner_isSome port)

theorem ConversionPayload.oldWire_occurs
    (payload : ConversionPayload input node)
    (port : Fin payload.oldFreePorts) :
    input.val.EndpointOccurs (payload.oldWire port)
      { node := node, port := .free port } := by
  obtain ⟨owner, howner⟩ := Option.isSome_iff_exists.mp
    (payload.oldOwner_isSome port)
  have hget := Option.get_of_eq_some (payload.oldOwner_isSome port) howner
  unfold ConversionPayload.oldWire
  rw [hget]
  exact Diagram.ConcreteElaboration.endpointOwner?_sound howner

def ConversionPayload.existingWire?
    (payload : ConversionPayload input node)
    (port : Fin payload.newFreePorts) : Option (Fin input.val.wireCount) :=
  match payload.findOldPort? port with
  | some old => some (payload.oldWire old)
  | none => findAttachment? payload.attachments port

theorem ConversionPayload.existingWire?_of_shared
    (payload : ConversionPayload input node)
    {port : Fin payload.newFreePorts} {old : Fin payload.oldFreePorts}
    (heq : payload.oldPort old = payload.newPort port) :
    ∃ owner, payload.existingWire? port = some owner ∧
      input.val.EndpointOccurs owner { node := node, port := .free old } := by
  obtain ⟨found, hfound⟩ := payload.findOldPort?_complete heq
  refine ⟨payload.oldWire found, by simp [ConversionPayload.existingWire?, hfound], ?_⟩
  have hsame : found = old := payload.oldPort_injective <|
    (payload.findOldPort?_sound hfound).trans heq.symm
  subst found
  exact payload.oldWire_occurs old

theorem ConversionPayload.existingWire?_of_attachment
    (payload : ConversionPayload input node)
    {port : Fin payload.newFreePorts} {wire : Fin input.val.wireCount}
    (hmem : (port, wire) ∈ payload.attachments) :
    payload.existingWire? port = some wire := by
  unfold ConversionPayload.existingWire?
  have hnone : payload.findOldPort? port = none := by
    cases hfind : payload.findOldPort? port with
    | none => rfl
    | some old =>
        exact False.elim <| payload.attachments_new_only port wire hmem
          ⟨old, payload.findOldPort?_sound hfind⟩
  rw [hnone]
  obtain ⟨found, hfound⟩ := findAttachment?_complete hmem
  have hfoundMem := findAttachment?_sound hfound
  have : found = wire := payload.attachments_functional port found wire
    hfoundMem hmem
  simpa [this] using hfound

private theorem HeadStripPayload.firstOwner_isSome
    (payload : HeadStripPayload input first second)
    (port : Fin payload.firstFreePorts) :
    (Diagram.ConcreteElaboration.endpointOwner? input.val
      { node := first, port := .free port }).isSome = true := by
  have hcovered := input.property.required_ports_are_covered first
  rw [payload.firstNode] at hcovered
  obtain ⟨wire, hwire⟩ := hcovered.2 port
  exact Option.isSome_iff_exists.mpr
    (Diagram.ConcreteElaboration.endpointOwner?_complete hwire)

private theorem HeadStripPayload.secondOwner_isSome
    (payload : HeadStripPayload input first second)
    (port : Fin payload.secondFreePorts) :
    (Diagram.ConcreteElaboration.endpointOwner? input.val
      { node := second, port := .free port }).isSome = true := by
  have hcovered := input.property.required_ports_are_covered second
  rw [payload.secondNode] at hcovered
  obtain ⟨wire, hwire⟩ := hcovered.2 port
  exact Option.isSome_iff_exists.mpr
    (Diagram.ConcreteElaboration.endpointOwner?_complete hwire)

def HeadStripPayload.firstWire
    (payload : HeadStripPayload input first second)
    (port : Fin payload.firstFreePorts) : Fin input.val.wireCount :=
  (Diagram.ConcreteElaboration.endpointOwner? input.val
    { node := first, port := .free port }).get
      (payload.firstOwner_isSome port)

def HeadStripPayload.secondWire
    (payload : HeadStripPayload input first second)
    (port : Fin payload.secondFreePorts) : Fin input.val.wireCount :=
  (Diagram.ConcreteElaboration.endpointOwner? input.val
    { node := second, port := .free port }).get
      (payload.secondOwner_isSome port)

theorem HeadStripPayload.firstWire_occurs
    (payload : HeadStripPayload input first second)
    (port : Fin payload.firstFreePorts) :
    input.val.EndpointOccurs (payload.firstWire port)
      { node := first, port := .free port } := by
  obtain ⟨owner, howner⟩ := Option.isSome_iff_exists.mp
    (payload.firstOwner_isSome port)
  have hget := Option.get_of_eq_some (payload.firstOwner_isSome port) howner
  unfold HeadStripPayload.firstWire
  rw [hget]
  exact Diagram.ConcreteElaboration.endpointOwner?_sound howner

theorem HeadStripPayload.secondWire_occurs
    (payload : HeadStripPayload input first second)
    (port : Fin payload.secondFreePorts) :
    input.val.EndpointOccurs (payload.secondWire port)
      { node := second, port := .free port } := by
  obtain ⟨owner, howner⟩ := Option.isSome_iff_exists.mp
    (payload.secondOwner_isSome port)
  have hget := Option.get_of_eq_some (payload.secondOwner_isSome port) howner
  unfold HeadStripPayload.secondWire
  rw [hget]
  exact Diagram.ConcreteElaboration.endpointOwner?_sound howner

theorem HeadStripPayload.shared_wire
    (payload : HeadStripPayload input first second)
    (left : Fin payload.firstFreePorts)
    (right : Fin payload.secondFreePorts)
    (heq : payload.firstPort left = payload.secondPort right) :
    payload.firstWire left = payload.secondWire right :=
  payload.shared_port_alignment left right (payload.firstWire left)
    (payload.secondWire right) heq (payload.firstWire_occurs left)
    (payload.secondWire_occurs right)

/-- The binary gate and the two selected occurrences determine the complete
equation wire, up to endpoint order. -/
theorem HeadStripPayload.outputEndpoints
    (payload : HeadStripPayload input first second) :
    (input.val.wires payload.outputWire).endpoints = [
        { node := first, port := .output },
        { node := second, port := .output }] ∨
      (input.val.wires payload.outputWire).endpoints = [
        { node := second, port := .output },
        { node := first, port := .output }] := by
  let endpoints := (input.val.wires payload.outputWire).endpoints
  have firstMem : ({ node := first, port := .output } :
      Diagram.CEndpoint input.val.nodeCount) ∈ endpoints := payload.firstOutput
  have secondMem : ({ node := second, port := .output } :
      Diagram.CEndpoint input.val.nodeCount) ∈ endpoints := payload.secondOutput
  have lengthEq : endpoints.length = 2 := payload.outputBinary
  have shape := endpoints.eq_getElem_of_length_eq_two lengthEq
  rw [shape] at firstMem secondMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMem secondMem
  rcases firstMem with firstHead | firstNext <;>
    rcases secondMem with secondHead | secondNext
  · exfalso
    apply payload.distinct
    exact congrArg Diagram.CEndpoint.node (firstHead.trans secondHead.symm)
  · left
    change endpoints = _
    rw [shape, ← firstHead, ← secondNext]
  · right
    change endpoints = _
    rw [shape, ← secondHead, ← firstNext]
  · exfalso
    apply payload.distinct
    exact congrArg Diagram.CEndpoint.node (firstNext.trans secondNext.symm)

/-- A selected term's free support can never be the binary output equation. -/
theorem HeadStripPayload.firstWire_ne_output
    (payload : HeadStripPayload input first second)
    (port : Fin payload.firstFreePorts) :
    payload.firstWire port ≠ payload.outputWire := by
  intro equality
  have occurs := payload.firstWire_occurs port
  rw [equality] at occurs
  rcases payload.outputEndpoints with forward | backward
  · simp [Diagram.ConcreteDiagram.EndpointOccurs, forward] at occurs
  · simp [Diagram.ConcreteDiagram.EndpointOccurs, backward] at occurs

/-- The second selected term's free support also survives output deletion. -/
theorem HeadStripPayload.secondWire_ne_output
    (payload : HeadStripPayload input first second)
    (port : Fin payload.secondFreePorts) :
    payload.secondWire port ≠ payload.outputWire := by
  intro equality
  have occurs := payload.secondWire_occurs port
  rw [equality] at occurs
  rcases payload.outputEndpoints with forward | backward
  · simp [Diagram.ConcreteDiagram.EndpointOccurs, forward] at occurs
  · simp [Diagram.ConcreteDiagram.EndpointOccurs, backward] at occurs

def HeadStripPayload.firstArgument
    (payload : HeadStripPayload input first second)
    (index : Fin payload.firstOriginalSpine.args.length) :
    Term 0 (Fin payload.firstFreePorts) :=
  prefixClose payload.firstOriginalSpine.binders
    (payload.firstOriginalSpine.args.get index)

def HeadStripPayload.secondArgument
    (payload : HeadStripPayload input first second)
    (index : Fin payload.firstOriginalSpine.args.length) :
    Term 0 (Fin payload.secondFreePorts) :=
  prefixClose payload.secondOriginalSpine.binders
    (payload.secondOriginalSpine.args.get
      (Fin.cast payload.sameArgumentCount index))

theorem HeadStripPayload.firstArgument_mapFree
    (payload : HeadStripPayload input first second)
    (index : Fin payload.firstOriginalSpine.args.length) :
    (payload.firstArgument index).mapFree payload.firstPort =
      prefixClose payload.firstOriginalSpine.binders
        ((payload.firstOriginalSpine.args.get index).mapFree
          payload.firstPort) := by
  unfold HeadStripPayload.firstArgument
  exact prefixClose_mapFree _ _ _

theorem HeadStripPayload.secondArgument_mapFree
    (payload : HeadStripPayload input first second)
    (index : Fin payload.firstOriginalSpine.args.length) :
    (payload.secondArgument index).mapFree payload.secondPort =
      prefixClose payload.secondOriginalSpine.binders
        ((payload.secondOriginalSpine.args.get
          (Fin.cast payload.sameArgumentCount index)).mapFree
            payload.secondPort) := by
  unfold HeadStripPayload.secondArgument
  exact prefixClose_mapFree _ _ _

def HeadStripPayload.argumentIndices
    (payload : HeadStripPayload input first second) :
    List (Fin payload.firstOriginalSpine.args.length) :=
  (allFin payload.firstOriginalSpine.args.length).filter fun index =>
    decide ((payload.firstArgument index).mapFree payload.firstPort ≠
      (payload.secondArgument index).mapFree payload.secondPort)

def headStripNodeDomain (input : Diagram.ConcreteDiagram)
    (first second : Fin input.nodeCount) :
    Diagram.SurvivorDomain input.nodeCount where
  survives node := decide (node ≠ first ∧ node ≠ second)

def headStripWireDomain (input : Diagram.ConcreteDiagram)
    (output : Fin input.wireCount) :
    Diagram.SurvivorDomain input.wireCount where
  survives wire := decide (wire ≠ output)

def headStripEndpoint?
    (domain : Diagram.SurvivorDomain nodes)
    (endpoint : Diagram.CEndpoint nodes) :
    Option (Diagram.CEndpoint domain.count) :=
  (domain.index? endpoint.node).map fun node =>
    { node := node, port := endpoint.port }

/-- Append-only semantic witness retained privately by the soundness proof.
The executable head-strip result is `headStripRaw` below. -/
def HeadStripPayload.firstAddedNode
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    Fin (input.val.nodeCount +
      (payload.argumentIndices.length + payload.argumentIndices.length)) :=
  Fin.natAdd input.val.nodeCount
    (Fin.castAdd payload.argumentIndices.length position)

def HeadStripPayload.secondAddedNode
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    Fin (input.val.nodeCount +
      (payload.argumentIndices.length + payload.argumentIndices.length)) :=
  Fin.natAdd input.val.nodeCount
    (Fin.natAdd payload.argumentIndices.length position)

def HeadStripPayload.firstReducedNode
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    Fin ((headStripNodeDomain input.val first second).count +
      (payload.argumentIndices.length + payload.argumentIndices.length)) :=
  Fin.natAdd (headStripNodeDomain input.val first second).count
    (Fin.castAdd payload.argumentIndices.length position)

def HeadStripPayload.secondReducedNode
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    Fin ((headStripNodeDomain input.val first second).count +
      (payload.argumentIndices.length + payload.argumentIndices.length)) :=
  Fin.natAdd (headStripNodeDomain input.val first second).count
    (Fin.natAdd payload.argumentIndices.length position)

def headStripLiftEndpoint (added : Nat)
    (endpoint : Diagram.CEndpoint nodes) : Diagram.CEndpoint (nodes + added) :=
  { node := Fin.castAdd added endpoint.node, port := endpoint.port }

def HeadStripPayload.firstAddedFreeEndpoints
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) :
    List (Diagram.CEndpoint (input.val.nodeCount +
      (payload.argumentIndices.length + payload.argumentIndices.length))) :=
  (allFin payload.argumentIndices.length).flatMap fun position =>
    let argument := payload.firstArgument (payload.argumentIndices.get position)
    (allFin argument.freeSupport.length).filterMap fun port =>
      let originalPort := argument.freeSupport.get port
      if payload.firstWire originalPort = wire then
        some { node := payload.firstAddedNode position, port := .free port }
      else
        none

def HeadStripPayload.secondAddedFreeEndpoints
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) :
    List (Diagram.CEndpoint (input.val.nodeCount +
      (payload.argumentIndices.length + payload.argumentIndices.length))) :=
  (allFin payload.argumentIndices.length).flatMap fun position =>
    let argument := payload.secondArgument (payload.argumentIndices.get position)
    (allFin argument.freeSupport.length).filterMap fun port =>
      let originalPort := argument.freeSupport.get port
      if payload.secondWire originalPort = wire then
        some { node := payload.secondAddedNode position, port := .free port }
      else
        none

/-- Append-only witness used to reuse the established forward decomposition
simulation. It is not returned by `applyHeadStrip`. -/
def headStripExpandedRaw (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Diagram.ConcreteDiagram where
  regionCount := input.val.regionCount
  nodeCount := input.val.nodeCount +
    (payload.argumentIndices.length + payload.argumentIndices.length)
  wireCount := input.val.wireCount + payload.argumentIndices.length
  root := input.val.root
  regions := input.val.regions
  nodes := Fin.addCases input.val.nodes fun fresh =>
    Fin.addCases
      (fun position =>
        let argument := payload.firstArgument
          (payload.argumentIndices.get position)
        .term payload.region argument.freeSupport.length argument.compact)
      (fun position =>
        let argument := payload.secondArgument
          (payload.argumentIndices.get position)
        .term payload.region argument.freeSupport.length argument.compact)
      fresh
  wires := Fin.addCases
    (fun wire =>
      let original := input.val.wires wire
      { scope := original.scope
        endpoints := original.endpoints.map
            (headStripLiftEndpoint
              (payload.argumentIndices.length + payload.argumentIndices.length)) ++
          payload.firstAddedFreeEndpoints wire ++
          payload.secondAddedFreeEndpoints wire })
    (fun position =>
      { scope := payload.region
        endpoints := [
          { node := payload.firstAddedNode position, port := .output },
          { node := payload.secondAddedNode position, port := .output }
        ] })

/-- Proof-only provenance for `headStripExpandedRaw`. The executable rule uses
`headStripWireProvenance` for the destructive result below. -/
def headStripExpandedWireProvenance (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    WireProvenance input.val (headStripExpandedRaw input payload) :=
  WireProvenance.append input.val (headStripExpandedRaw input payload)
    payload.argumentIndices.length rfl

/-- Proof-only interface transport for `headStripExpandedRaw`. -/
def headStripExpandedInterfaceTransport (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    InterfaceTransport input.val (headStripExpandedRaw input payload) :=
  InterfaceTransport.append input.val (headStripExpandedRaw input payload)
    payload.argumentIndices.length rfl

def HeadStripPayload.firstReducedFreeEndpoints
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) :
    List (Diagram.CEndpoint ((headStripNodeDomain input.val first second).count +
      (payload.argumentIndices.length + payload.argumentIndices.length))) :=
  (allFin payload.argumentIndices.length).flatMap fun position =>
    let argument := payload.firstArgument (payload.argumentIndices.get position)
    (allFin argument.freeSupport.length).filterMap fun port =>
      let originalPort := argument.freeSupport.get port
      if payload.firstWire originalPort = wire then
        some { node := payload.firstReducedNode position, port := .free port }
      else
        none

def HeadStripPayload.secondReducedFreeEndpoints
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) :
    List (Diagram.CEndpoint ((headStripNodeDomain input.val first second).count +
      (payload.argumentIndices.length + payload.argumentIndices.length))) :=
  (allFin payload.argumentIndices.length).flatMap fun position =>
    let argument := payload.secondArgument (payload.argumentIndices.get position)
    (allFin argument.freeSupport.length).filterMap fun port =>
      let originalPort := argument.freeSupport.get port
      if payload.secondWire originalPort = wire then
        some { node := payload.secondReducedNode position, port := .free port }
      else
        none

/-- Replace a binary rigid-head equation with exactly its nontrivial argument
equations. The original term nodes and their equation wire do not survive. -/
def headStripRaw (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Diagram.ConcreteDiagram where
  regionCount := input.val.regionCount
  nodeCount := (headStripNodeDomain input.val first second).count +
    (payload.argumentIndices.length + payload.argumentIndices.length)
  wireCount := (headStripWireDomain input.val payload.outputWire).count +
    payload.argumentIndices.length
  root := input.val.root
  regions := input.val.regions
  nodes := Fin.addCases
    (fun node => input.val.nodes
      ((headStripNodeDomain input.val first second).origin node)) fun fresh =>
    Fin.addCases
      (fun position =>
        let argument := payload.firstArgument
          (payload.argumentIndices.get position)
        .term payload.region argument.freeSupport.length argument.compact)
      (fun position =>
        let argument := payload.secondArgument
          (payload.argumentIndices.get position)
        .term payload.region argument.freeSupport.length argument.compact)
      fresh
  wires := Fin.addCases
    (fun wire =>
      let originalId :=
        (headStripWireDomain input.val payload.outputWire).origin wire
      let original := input.val.wires originalId
      { scope := original.scope
        endpoints := (original.endpoints.filterMap
            (headStripEndpoint? (headStripNodeDomain input.val first second))).map
              (headStripLiftEndpoint
                (payload.argumentIndices.length + payload.argumentIndices.length)) ++
          payload.firstReducedFreeEndpoints originalId ++
          payload.secondReducedFreeEndpoints originalId })
    (fun position =>
      { scope := payload.region
        endpoints := [
          { node := payload.firstReducedNode position, port := .output },
          { node := payload.secondReducedNode position, port := .output }
        ] })

def headStripWireProvenance (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    WireProvenance input.val (headStripRaw input payload) :=
  let domain := headStripWireDomain input.val payload.outputWire
  WireProvenance.rootFiltered input.val (headStripRaw input payload)
    (fun wire => (domain.index? wire).map fun compact =>
      Fin.castAdd payload.argumentIndices.length compact) (by
        intro left right mapped hleft hright
        rw [Option.map_eq_some_iff] at hleft hright
        obtain ⟨leftIndex, hleftIndex, hleftMapped⟩ := hleft
        obtain ⟨rightIndex, hrightIndex, hrightMapped⟩ := hright
        have indexEq : leftIndex = rightIndex := by
          apply Fin.ext
          simpa using congrArg Fin.val (hleftMapped.trans hrightMapped.symm)
        subst rightIndex
        have leftOrigin := (domain.index?_eq_some_iff left leftIndex).mp hleftIndex
        have rightOrigin := (domain.index?_eq_some_iff right leftIndex).mp hrightIndex
        exact leftOrigin.symm.trans rightOrigin)

def headStripInterfaceTransport (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    InterfaceTransport input.val (headStripRaw input payload) :=
  let domain := headStripWireDomain input.val payload.outputWire
  InterfaceTransport.rootFiltered input.val (headStripRaw input payload)
    (fun wire => (domain.index? wire).map fun compact =>
      Fin.castAdd payload.argumentIndices.length compact)

def applyHeadStrip (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Except StepError (StepReceipt input) :=
  match hcheck : Diagram.checkWellFormed signature
      (headStripRaw input payload) with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (StepReceipt.ofChecked input
      (headStripRaw input payload) (headStripWireProvenance input payload)
      (headStripInterfaceTransport input payload) result hcheck)

theorem applyHeadStrip_preserves_raw
    (happly : applyHeadStrip input payload = .ok result) :
    result.result.val = headStripRaw input payload := by
  unfold applyHeadStrip at happly
  split at happly
  · contradiction
  · rename_i checked hcheck
    cases happly
    exact Diagram.checkWellFormed_preserves_input hcheck

theorem applyHeadStrip_realizes
    (happly : applyHeadStrip input payload = .ok result) :
    result.Realizes (headStripRaw input payload)
      (headStripWireProvenance input payload)
      (headStripInterfaceTransport input payload) := by
  unfold applyHeadStrip at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

def anchorAvailableAt (input : Diagram.ConcreteDiagram)
    (wireScope witnessRegion target : Fin input.regionCount) : Bool :=
  (allFin input.regionCount).any fun available =>
    decide (input.Encloses wireScope available ∧
      input.Encloses available witnessRegion ∧
      concreteCutDepth input available = concreteCutDepth input witnessRegion ∧
      input.Encloses available target)

private def anchoredSplitLiftEndpoint
    (endpoint : Diagram.CEndpoint nodes) : Diagram.CEndpoint (nodes + 1) :=
  { node := endpoint.node.castSucc, port := endpoint.port }

@[simp] theorem anchoredSplitLiftEndpoint_node
    (endpoint : Diagram.CEndpoint nodes) :
    (anchoredSplitLiftEndpoint endpoint).node = endpoint.node.castSucc := rfl

@[simp] theorem anchoredSplitLiftEndpoint_port
    (endpoint : Diagram.CEndpoint nodes) :
    (anchoredSplitLiftEndpoint endpoint).port = endpoint.port := rfl

def anchoredWireSplitRaw (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (endpoints : List (Diagram.CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Term 0 (Fin 0)) : Diagram.ConcreteDiagram where
  regionCount := input.val.regionCount
  nodeCount := input.val.nodeCount + 1
  wireCount := input.val.wireCount + 1
  root := input.val.root
  regions := input.val.regions
  nodes := Fin.lastCases (.term target 0 term) input.val.nodes
  wires := Fin.lastCases
    { scope := target
      endpoints := { node := Fin.last input.val.nodeCount, port := .output } ::
        endpoints.map anchoredSplitLiftEndpoint }
    (fun candidate =>
      let original := input.val.wires candidate
      { scope := original.scope
        endpoints := (if candidate = wire then
            original.endpoints.filter fun endpoint => decide (endpoint ∉ endpoints)
          else
            original.endpoints).map anchoredSplitLiftEndpoint })

def anchoredWireSplitProvenance (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (endpoints : List (Diagram.CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Term 0 (Fin 0)) :
    WireProvenance input.val
      (anchoredWireSplitRaw input wire endpoints target term) :=
  WireProvenance.append input.val
    (anchoredWireSplitRaw input wire endpoints target term) 1 rfl

/-- Logical transport for anchored split retains every old identity on the
old-wire branch. The newly appended factor wire remains fresh and internal. -/
def anchoredWireSplitInterfaceTransport
    (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (endpoints : List (Diagram.CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Term 0 (Fin 0)) :
    InterfaceTransport input.val
      (anchoredWireSplitRaw input wire endpoints target term) :=
  InterfaceTransport.append input.val
    (anchoredWireSplitRaw input wire endpoints target term) 1 rfl

def applyAnchoredWireSplit (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (witness : Fin input.val.nodeCount)
    (endpoints : List (Diagram.CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) :
    Except StepError (StepReceipt input) :=
  match input.val.nodes witness with
  | .term witnessRegion 0 term =>
      if hwitness : input.val.EndpointOccurs wire
          { node := witness, port := .output } then
        if hnodup : endpoints.Nodup then
          if hsubset : ∀ endpoint, endpoint ∈ endpoints →
              input.val.EndpointOccurs wire endpoint then
            if hkeeps : { node := witness, port := Diagram.CPort.output } ∉
                endpoints then
              if htarget : ∀ endpoint, endpoint ∈ endpoints →
                  input.val.Encloses target
                    (input.val.nodes endpoint.node).region then
                if havailable : anchorAvailableAt input.val
                    (input.val.wires wire).scope witnessRegion target then
                    match hcheck : Diagram.checkWellFormed signature
                        (anchoredWireSplitRaw input wire endpoints target term) with
                    | .error error => .error (.resultNotWellFormed error)
                    | .ok result => .ok (StepReceipt.ofChecked input
                        (anchoredWireSplitRaw input wire endpoints target term)
                        (anchoredWireSplitProvenance input wire endpoints target term)
                        (anchoredWireSplitInterfaceTransport input wire endpoints
                          target term) result hcheck)
                else .error .binderEscape
              else .error .binderEscape
            else .error .invalidSelection
          else .error .invalidSelection
        else .error .invalidSelection
      else .error .invalidWire
  | .term _ (_ + 1) _ => .error .openTermRequired
  | .atom .. | .named .. => .error .invalidNode

theorem applyAnchoredWireSplit_success_shape
    (happly : applyAnchoredWireSplit input wire witness endpoints target =
      .ok result) :
    ∃ witnessRegion term,
      input.val.nodes witness = .term witnessRegion 0 term ∧
      result.result.val = anchoredWireSplitRaw input wire endpoints target term := by
  unfold applyAnchoredWireSplit at happly
  split at happly <;> try contradiction
  rename_i witnessRegion term hterm
  repeat' first | split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨witnessRegion, term, hterm,
    Diagram.checkWellFormed_preserves_input hcheck⟩

theorem applyAnchoredWireSplit_realizes
    (happly : applyAnchoredWireSplit input wire witness endpoints target =
      .ok result) :
    ∃ witnessRegion term,
      input.val.nodes witness = .term witnessRegion 0 term ∧
      result.Realizes (anchoredWireSplitRaw input wire endpoints target term)
        (anchoredWireSplitProvenance input wire endpoints target term)
        (anchoredWireSplitInterfaceTransport input wire endpoints target term) := by
  unfold applyAnchoredWireSplit at happly
  split at happly <;> try contradiction
  rename_i witnessRegion term hterm
  repeat' first | split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨witnessRegion, term, hterm,
    StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

theorem applyAnchoredWireSplit_success {signature : List Nat}
    (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (witness : Fin input.val.nodeCount)
    (endpoints : List (Diagram.CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (result : StepReceipt input)
    (happly : applyAnchoredWireSplit input wire witness endpoints target =
      .ok result) :
    ∃ witnessRegion term,
      input.val.nodes witness = .term witnessRegion 0 term ∧
      input.val.EndpointOccurs wire
        { node := witness, port := .output } ∧
      endpoints.Nodup ∧
      (∀ endpoint : Diagram.CEndpoint input.val.nodeCount,
        endpoint ∈ endpoints →
        input.val.EndpointOccurs wire endpoint) ∧
      { node := witness, port := Diagram.CPort.output } ∉ endpoints ∧
      (∀ endpoint : Diagram.CEndpoint input.val.nodeCount,
        endpoint ∈ endpoints →
        input.val.Encloses target (input.val.nodes endpoint.node).region) ∧
      anchorAvailableAt input.val (input.val.wires wire).scope
        witnessRegion target = true ∧
      result.result.val = anchoredWireSplitRaw input wire endpoints target term := by
  unfold applyAnchoredWireSplit at happly
  split at happly <;> try contradiction
  rename_i witnessRegion term hterm
  split at happly <;> try contradiction
  rename_i hwitness
  split at happly <;> try contradiction
  rename_i hnodup
  split at happly <;> try contradiction
  rename_i hsubset
  split at happly <;> try contradiction
  rename_i hkeeps
  split at happly <;> try contradiction
  rename_i htarget
  split at happly <;> try contradiction
  rename_i havailable
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨witnessRegion, term, hterm, hwitness, hnodup, hsubset, hkeeps,
    htarget, havailable, Diagram.checkWellFormed_preserves_input hcheck⟩

def anchoredContractNodeDomain (input : Diagram.ConcreteDiagram)
    (redundant : Fin input.nodeCount) : Diagram.SurvivorDomain input.nodeCount where
  survives node := decide (node ≠ redundant)

def anchoredContractWireDomain (input : Diagram.ConcreteDiagram)
    (drop : Fin input.wireCount) : Diagram.SurvivorDomain input.wireCount where
  survives wire := decide (wire ≠ drop)

def anchoredContractEndpoint?
    (domain : Diagram.SurvivorDomain nodes)
    (endpoint : Diagram.CEndpoint nodes) :
    Option (Diagram.CEndpoint domain.count) :=
  (domain.index? endpoint.node).map fun node =>
    { node := node, port := endpoint.port }

def anchoredWireContractRaw (input : Diagram.CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount) : Diagram.ConcreteDiagram :=
  let nodes := anchoredContractNodeDomain input.val redundant
  let wires := anchoredContractWireDomain input.val drop
  let moved := (input.val.wires drop).endpoints.filter fun endpoint =>
    decide (endpoint ≠ { node := redundant, port := Diagram.CPort.output })
  { regionCount := input.val.regionCount
    nodeCount := nodes.count
    wireCount := wires.count
    root := input.val.root
    regions := input.val.regions
    nodes := fun node => input.val.nodes (nodes.origin node)
    wires := fun wire =>
      let originalId := wires.origin wire
      let original := input.val.wires originalId
      { scope := original.scope
        endpoints :=
          (if originalId = keep then original.endpoints ++ moved
            else original.endpoints).filterMap
              (anchoredContractEndpoint? nodes) } }

def anchoredWireContractProvenance (input : Diagram.CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount) :
    WireProvenance input.val
      (anchoredWireContractRaw input redundant drop keep) :=
  WireProvenance.survivors input.val
    (anchoredWireContractRaw input redundant drop keep)
    (anchoredContractWireDomain input.val drop) rfl

/-- The executor-side semantic gate for exposing a contracted identity at the
ordered-open root.  Naming the gate keeps the receipt map and its soundness
proof on the same Boolean decision. -/
def anchoredContractRootAvailable
    (input : Diagram.CheckedDiagram signature)
    (survivor : Fin input.val.nodeCount)
    (keep : Fin input.val.wireCount) : Bool :=
  match input.val.nodes survivor with
  | .term survivorRegion _ _ => anchorAvailableAt input.val
      (input.val.wires keep).scope survivorRegion input.val.root
  | _ => false

/-- Logical transport for anchored contraction. The removed redundant output
identity coalesces with the retained output identity exactly when the
survivor's closed equality is available at the ordered-open root. Graph
provenance continues to omit the removed identity to remain injective. -/
def anchoredWireContractInterfaceTransport
    (input : Diagram.CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount) :
    InterfaceTransport input.val
      (anchoredWireContractRaw input redundant drop keep) :=
  let domain := anchoredContractWireDomain input.val drop
  let rootAvailable := anchoredContractRootAvailable input survivor keep
  InterfaceTransport.rootFiltered input.val
    (anchoredWireContractRaw input redundant drop keep)
    (fun wire =>
      if rootAvailable then
        if wire = drop then domain.index? keep else domain.index? wire
      else domain.index? wire)

/-- Regression witness for the distinction between graph provenance and the
logical interface. Contraction removes `drop` from the concrete carrier, but
both ordered boundary positions are transported to the retained `keep`
identity. -/
theorem anchoredWireContract_interface_coalesces
    (input : Diagram.CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (survivorRegion : Fin input.val.regionCount)
    (survivorTerm : Lambda.Term 0 (Fin 0))
    (hsurvivor : input.val.nodes survivor =
      .term survivorRegion 0 survivorTerm)
    (havailable : anchorAvailableAt input.val (input.val.wires keep).scope
      survivorRegion input.val.root = true)
    (hdistinct : drop ≠ keep)
    (hkeepRoot : (input.val.wires keep).scope = input.val.root) :
    ∃ mapped,
      (anchoredWireContractProvenance input redundant drop keep).image? drop =
          none ∧
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep).image?
          drop = some mapped ∧
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep).image?
          keep = some mapped ∧
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep).transportBoundary
        [drop, keep] = some [mapped, mapped] := by
  let domain := anchoredContractWireDomain input.val drop
  have hkeep : domain.survives keep = true := by
    simp [domain, anchoredContractWireDomain, hdistinct.symm]
  let mapped := domain.index keep hkeep
  have hindex : domain.index? keep = some mapped := by
    exact domain.index?_index keep hkeep
  have hindex' :
      (anchoredContractWireDomain input.val drop).index? keep = some mapped := by
    simpa [domain] using hindex
  have htargetRoot :
      ((anchoredWireContractRaw input redundant drop keep).wires mapped).scope =
        (anchoredWireContractRaw input redundant drop keep).root := by
    change (input.val.wires (domain.origin mapped)).scope = input.val.root
    rw [show domain.origin mapped = keep from domain.origin_index keep hkeep]
    exact hkeepRoot
  have hprovenanceDrop :
      (anchoredWireContractProvenance input redundant drop keep).image? drop =
        none := by
    have hdrop' :
        (anchoredContractWireDomain input.val drop).index? drop = none := by
      simp [anchoredContractWireDomain]
    simp [anchoredWireContractProvenance, WireProvenance.survivors,
      WireProvenance.rootFiltered, hdrop']
  have hinterfaceDrop :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep).image?
        drop = some mapped := by
    unfold anchoredWireContractInterfaceTransport
      InterfaceTransport.rootFiltered
    dsimp only
    rw [show anchoredContractRootAvailable input survivor keep = true by
      simpa [anchoredContractRootAvailable, hsurvivor] using havailable,
      if_pos rfl, hindex']
    simp only [if_pos rfl]
    change (if
      ((anchoredWireContractRaw input redundant drop keep).wires mapped).scope =
          (anchoredWireContractRaw input redundant drop keep).root then
        some mapped else none) = some mapped
    rw [if_pos htargetRoot]
  have hinterfaceKeep :
      (anchoredWireContractInterfaceTransport input redundant survivor drop keep).image?
        keep = some mapped := by
    unfold anchoredWireContractInterfaceTransport
      InterfaceTransport.rootFiltered
    dsimp only
    rw [show anchoredContractRootAvailable input survivor keep = true by
      simpa [anchoredContractRootAvailable, hsurvivor] using havailable,
      if_neg hdistinct.symm, hindex']
    change (if
      ((anchoredWireContractRaw input redundant drop keep).wires mapped).scope =
          (anchoredWireContractRaw input redundant drop keep).root then
        some mapped else none) = some mapped
    rw [if_pos htargetRoot]
  refine ⟨mapped, hprovenanceDrop, hinterfaceDrop, hinterfaceKeep, ?_⟩
  simp [InterfaceTransport.transportBoundary, hinterfaceDrop, hinterfaceKeep]
  rfl

/-- A cut-shielded survivor cannot justify coalescing an exposed dropped
identity; the dropped boundary position therefore has no semantic image. -/
theorem anchoredWireContract_interface_drops_unavailable
    (input : Diagram.CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (survivorRegion : Fin input.val.regionCount)
    (survivorTerm : Lambda.Term 0 (Fin 0))
    (hsurvivor : input.val.nodes survivor =
      .term survivorRegion 0 survivorTerm)
    (hunavailable : anchorAvailableAt input.val (input.val.wires keep).scope
      survivorRegion input.val.root = false) :
    (anchoredWireContractInterfaceTransport input redundant survivor drop keep
      ).image? drop = none := by
  let domain := anchoredContractWireDomain input.val drop
  have hdrop : domain.index? drop = none := by
    rw [domain.index?_eq_none_iff]
    simp [domain, anchoredContractWireDomain]
  unfold anchoredWireContractInterfaceTransport
    InterfaceTransport.rootFiltered
  dsimp only
  rw [show anchoredContractRootAvailable input survivor keep = false by
    simpa [anchoredContractRootAvailable, hsurvivor] using hunavailable, hdrop]
  rfl

def applyAnchoredWireContract (input : Diagram.CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (certificate : Lambda.Certificate) :
    Except StepError (StepReceipt input) :=
  if redundant = survivor then .error .invalidSelection
  else
    match input.val.nodes redundant, input.val.nodes survivor with
    | .term redundantRegion 0 redundantTerm,
        .term survivorRegion 0 survivorTerm =>
        if Lambda.checkCertificate redundantTerm survivorTerm certificate then
          match Diagram.ConcreteElaboration.endpointOwner? input.val
              { node := redundant, port := .output },
            Diagram.ConcreteElaboration.endpointOwner? input.val
              { node := survivor, port := .output } with
          | some drop, some keep =>
              if drop = keep then .error .selfWire
              else if concreteCutDepth input.val (input.val.wires drop).scope =
                  concreteCutDepth input.val redundantRegion then
                let moved := (input.val.wires drop).endpoints.filter fun endpoint =>
                  decide (endpoint ≠
                    { node := redundant, port := Diagram.CPort.output })
                if moved.all fun endpoint => anchorAvailableAt input.val
                    (input.val.wires keep).scope survivorRegion
                    (input.val.nodes endpoint.node).region then
                  match hcheck : Diagram.checkWellFormed signature
                      (anchoredWireContractRaw input redundant drop keep) with
                  | .error error => .error (.resultNotWellFormed error)
                  | .ok result => .ok (StepReceipt.ofChecked input
                      (anchoredWireContractRaw input redundant drop keep)
                      (anchoredWireContractProvenance input redundant drop keep)
                      (anchoredWireContractInterfaceTransport input redundant
                        survivor drop keep) result hcheck)
                else .error .binderEscape
              else .error .binderEscape
          | _, _ => .error .invalidWire
        else .error .invalidCertificate
    | .term _ (_ + 1) _, _ | _, .term _ (_ + 1) _ =>
        .error .openTermRequired
    | _, _ => .error .invalidNode

theorem applyAnchoredWireContract_success_shape
    (happly : applyAnchoredWireContract input redundant survivor certificate =
      .ok result) :
    ∃ drop keep,
      Diagram.ConcreteElaboration.endpointOwner? input.val
          { node := redundant, port := .output } = some drop ∧
      Diagram.ConcreteElaboration.endpointOwner? input.val
          { node := survivor, port := .output } = some keep ∧
      result.result.val = anchoredWireContractRaw input redundant drop keep := by
  unfold applyAnchoredWireContract at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i drop keep hdrop hkeep
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  dsimp only at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨drop, keep, hdrop, hkeep,
    Diagram.checkWellFormed_preserves_input hcheck⟩

theorem applyAnchoredWireContract_realizes
    (happly : applyAnchoredWireContract input redundant survivor certificate =
      .ok result) :
    ∃ drop keep,
      Diagram.ConcreteElaboration.endpointOwner? input.val
          { node := redundant, port := .output } = some drop ∧
      Diagram.ConcreteElaboration.endpointOwner? input.val
          { node := survivor, port := .output } = some keep ∧
      result.Realizes (anchoredWireContractRaw input redundant drop keep)
        (anchoredWireContractProvenance input redundant drop keep)
        (anchoredWireContractInterfaceTransport input redundant survivor drop keep) := by
  unfold applyAnchoredWireContract at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i drop keep hdrop hkeep
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  dsimp only at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨drop, keep, hdrop, hkeep,
    StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

theorem applyAnchoredWireContract_success {signature : List Nat}
    (input : Diagram.CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (certificate : Lambda.Certificate) (result : StepReceipt input)
    (happly : applyAnchoredWireContract input redundant survivor certificate =
      .ok result) :
    ∃ redundantRegion redundantTerm survivorRegion survivorTerm drop keep,
      redundant ≠ survivor ∧
      input.val.nodes redundant = .term redundantRegion 0 redundantTerm ∧
      input.val.nodes survivor = .term survivorRegion 0 survivorTerm ∧
      Lambda.checkCertificate redundantTerm survivorTerm certificate = true ∧
      Diagram.ConcreteElaboration.endpointOwner? input.val
        { node := redundant, port := .output } = some drop ∧
      Diagram.ConcreteElaboration.endpointOwner? input.val
        { node := survivor, port := .output } = some keep ∧
      drop ≠ keep ∧
      concreteCutDepth input.val (input.val.wires drop).scope =
        concreteCutDepth input.val redundantRegion ∧
      ((input.val.wires drop).endpoints.filter fun endpoint =>
        decide (endpoint ≠
          { node := redundant, port := Diagram.CPort.output })).all
        (fun endpoint => anchorAvailableAt input.val
          (input.val.wires keep).scope survivorRegion
          (input.val.nodes endpoint.node).region) = true ∧
      result.result.val =
        anchoredWireContractRaw input redundant drop keep := by
  unfold applyAnchoredWireContract at happly
  split at happly <;> try contradiction
  rename_i hdistinct
  split at happly <;> try contradiction
  rename_i redundantRegion redundantTerm survivorRegion survivorTerm
    hre hsu
  split at happly <;> try contradiction
  rename_i hcertificate
  split at happly <;> try contradiction
  rename_i drop keep hdrop hkeep
  split at happly <;> try contradiction
  rename_i hdifferent
  split at happly <;> try contradiction
  rename_i hdepth
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i havailable
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨redundantRegion, redundantTerm, survivorRegion, survivorTerm,
    drop, keep, hdistinct, hre, hsu, hcertificate, hdrop, hkeep, hdifferent,
    hdepth, havailable, Diagram.checkWellFormed_preserves_input hcheck⟩

def fusionNodeDomain (input : Diagram.ConcreteDiagram)
    (producer : Fin input.nodeCount) : Diagram.SurvivorDomain input.nodeCount where
  survives node := decide (node ≠ producer)

def fusionWireDomain (input : Diagram.ConcreteDiagram)
    (consumed : Fin input.wireCount) : Diagram.SurvivorDomain input.wireCount where
  survives wire := decide (wire ≠ consumed)

private def fusionKeepEndpoint (producer consumer : Fin nodes)
    (endpoint : Diagram.CEndpoint nodes) : Bool :=
  if endpoint.node = producer then false
  else if endpoint.node = consumer then
    match endpoint.port with
    | .free _ => false
    | _ => true
  else true

@[simp] theorem fusionKeepEndpoint_consumer_free
    (producer consumer : Fin nodes) (port : Nat) :
    fusionKeepEndpoint producer consumer
      { node := consumer, port := Diagram.CPort.free port } = false := by
  simp [fusionKeepEndpoint]

def fusionTerm (producerTerm : Term 0 (Fin producerPorts))
    (consumerTerm : Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin wires)
    (consumerWire : Fin consumerPorts → Fin wires)
    (consumedPort : Fin consumerPorts) : Term 0 (Fin wires) :=
  consumerTerm.bindFree fun port =>
    if port = consumedPort then producerTerm.mapFree producerWire
    else .port (consumerWire port)

def fusionRaw (input : Diagram.CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Term 0 (Fin producerPorts))
    (consumerTerm : Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts) : Diagram.ConcreteDiagram :=
  let nodes := fusionNodeDomain input.val producer
  let wires := fusionWireDomain input.val consumedWire
  let mergedGlobal := fusionTerm producerTerm consumerTerm producerWire
    consumerWire consumedPort
  let merged := mergedGlobal.compact
  let mappedConsumer := nodes.index consumer (by
    exact decide_eq_true hdistinct.symm)
  { regionCount := input.val.regionCount
    nodeCount := nodes.count
    wireCount := wires.count
    root := input.val.root
    regions := input.val.regions
    nodes := fun node =>
      let original := nodes.origin node
      if original = consumer then
        .term consumerRegion mergedGlobal.freeSupport.length merged
      else input.val.nodes original
    wires := fun wire =>
      let originalId := wires.origin wire
      let original := input.val.wires originalId
      { scope := original.scope
        endpoints :=
          (original.endpoints.filterMap fun endpoint =>
              if fusionKeepEndpoint producer consumer endpoint then
                anchoredContractEndpoint? nodes endpoint
              else none)
          ++ (allFin mergedGlobal.freeSupport.length).filterMap fun port =>
            if mergedGlobal.freeSupport.get port = originalId then
              some { node := mappedConsumer, port := Diagram.CPort.free port }
            else none } }

def fusionWireProvenance (input : Diagram.CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Term 0 (Fin producerPorts))
    (consumerTerm : Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts) :
    WireProvenance input.val
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort) :=
  WireProvenance.survivors input.val
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort)
    (fusionWireDomain input.val consumedWire) rfl

/-- Fusion truly consumes its connecting wire; every other old identity is
transported through stable survivor compaction. -/
def fusionInterfaceTransport (input : Diagram.CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Term 0 (Fin producerPorts))
    (consumerTerm : Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts) :
    InterfaceTransport input.val
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort) :=
  InterfaceTransport.survivors input.val
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort)
    (fusionWireDomain input.val consumedWire) rfl

def resolveNodeFreeWires?
    (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (ports : Nat) :
    Option (Fin ports → Fin input.val.wireCount) :=
  sequenceFin fun port =>
    Diagram.ConcreteElaboration.endpointOwner? input.val
      { node := node, port := .free port }

def applyFusionOrdered (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount) (consumedPortIndex : Nat) :
    Except StepError (StepReceipt input) :=
  if hdistinct : producer ≠ consumer then
    match input.val.nodes producer, input.val.nodes consumer with
    | .term producerRegion producerPorts producerTerm,
        .term consumerRegion consumerPorts consumerTerm =>
        if hscope : producerRegion = (input.val.wires wire).scope then
          if hport : consumedPortIndex < consumerPorts then
            let consumedPort : Fin consumerPorts := ⟨consumedPortIndex, hport⟩
            match resolveNodeFreeWires? input producer producerPorts,
                resolveNodeFreeWires? input consumer consumerPorts with
            | some producerWires, some consumerWires =>
                match hcheck : Diagram.checkWellFormed signature
                    (fusionRaw input wire producer consumer hdistinct
                      consumerRegion producerTerm consumerTerm producerWires
                      consumerWires consumedPort) with
                | .error error => .error (.resultNotWellFormed error)
                | .ok result => .ok (StepReceipt.ofChecked input
                    (fusionRaw input wire producer consumer hdistinct
                      consumerRegion producerTerm consumerTerm producerWires
                      consumerWires consumedPort)
                    (fusionWireProvenance input wire producer consumer hdistinct
                      consumerRegion producerTerm consumerTerm producerWires
                      consumerWires consumedPort)
                    (fusionInterfaceTransport input wire producer consumer
                      hdistinct consumerRegion producerTerm consumerTerm
                      producerWires consumerWires consumedPort) result hcheck)
            | _, _ => .error .invalidWire
          else .error .arityMismatch
        else .error .binderEscape
    | _, _ => .error .invalidNode
  else .error .invalidSelection

def applyFusion (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount) :
    Except StepError (StepReceipt input) :=
  match (input.val.wires wire).endpoints with
  | [first, second] =>
      match first.port, second.port with
      | .output, .free consumed =>
          applyFusionOrdered input wire first.node second.node consumed
      | .free consumed, .output =>
          applyFusionOrdered input wire second.node first.node consumed
      | _, _ => .error .invalidSelection
  | _ => .error .invalidSelection

theorem applyFusionOrdered_success
    (happly : applyFusionOrdered input wire producer consumer
      consumedPortIndex = .ok result) :
    ∃ (hdistinct : producer ≠ consumer)
      (producerRegion : Fin input.val.regionCount)
      (producerPorts : Nat) (producerTerm : Term 0 (Fin producerPorts))
      (consumerRegion : Fin input.val.regionCount)
      (consumerPorts : Nat) (consumerTerm : Term 0 (Fin consumerPorts))
      (hport : consumedPortIndex < consumerPorts)
      (producerWires : Fin producerPorts → Fin input.val.wireCount)
      (consumerWires : Fin consumerPorts → Fin input.val.wireCount),
      input.val.nodes producer =
          .term producerRegion producerPorts producerTerm ∧
      input.val.nodes consumer =
          .term consumerRegion consumerPorts consumerTerm ∧
      producerRegion = (input.val.wires wire).scope ∧
      resolveNodeFreeWires? input producer producerPorts = some producerWires ∧
      resolveNodeFreeWires? input consumer consumerPorts = some consumerWires ∧
      result.result.val = fusionRaw input wire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWires consumerWires
        ⟨consumedPortIndex, hport⟩ := by
  unfold applyFusionOrdered at happly
  split at happly <;> try contradiction
  rename_i hdistinct
  split at happly <;> try contradiction
  rename_i producerRegion producerPorts producerTerm consumerRegion
    consumerPorts consumerTerm hproducer hconsumer
  split at happly <;> try contradiction
  rename_i hscope
  split at happly <;> try contradiction
  rename_i hport
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i producerWires consumerWires hproducerWires hconsumerWires
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨hdistinct, producerRegion, producerPorts, producerTerm,
    consumerRegion, consumerPorts, consumerTerm, hport, producerWires,
    consumerWires, hproducer, hconsumer, hscope, hproducerWires,
    hconsumerWires, Diagram.checkWellFormed_preserves_input hcheck⟩

theorem applyFusionOrdered_realizes
    (happly : applyFusionOrdered input wire producer consumer
      consumedPortIndex = .ok result) :
    ∃ (hdistinct : producer ≠ consumer)
      (producerRegion : Fin input.val.regionCount)
      (producerPorts : Nat) (producerTerm : Term 0 (Fin producerPorts))
      (consumerRegion : Fin input.val.regionCount)
      (consumerPorts : Nat) (consumerTerm : Term 0 (Fin consumerPorts))
      (hport : consumedPortIndex < consumerPorts)
      (producerWires : Fin producerPorts → Fin input.val.wireCount)
      (consumerWires : Fin consumerPorts → Fin input.val.wireCount),
      input.val.nodes producer =
          .term producerRegion producerPorts producerTerm ∧
      input.val.nodes consumer =
          .term consumerRegion consumerPorts consumerTerm ∧
      producerRegion = (input.val.wires wire).scope ∧
      resolveNodeFreeWires? input producer producerPorts = some producerWires ∧
      resolveNodeFreeWires? input consumer consumerPorts = some consumerWires ∧
      result.Realizes
        (fusionRaw input wire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWires consumerWires
          ⟨consumedPortIndex, hport⟩)
        (fusionWireProvenance input wire producer consumer hdistinct
          consumerRegion producerTerm consumerTerm producerWires consumerWires
          ⟨consumedPortIndex, hport⟩)
        (fusionInterfaceTransport input wire producer consumer hdistinct
          consumerRegion producerTerm consumerTerm producerWires consumerWires
          ⟨consumedPortIndex, hport⟩) := by
  unfold applyFusionOrdered at happly
  split at happly <;> try contradiction
  rename_i hdistinct
  split at happly <;> try contradiction
  rename_i producerRegion producerPorts producerTerm consumerRegion
    consumerPorts consumerTerm hproducer hconsumer
  split at happly <;> try contradiction
  rename_i hscope
  split at happly <;> try contradiction
  rename_i hport
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i producerWires consumerWires hproducerWires hconsumerWires
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨hdistinct, producerRegion, producerPorts, producerTerm,
    consumerRegion, consumerPorts, consumerTerm, hport, producerWires,
    consumerWires, hproducer, hconsumer, hscope, hproducerWires,
    hconsumerWires, StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

theorem applyFusion_success
    (happly : applyFusion input wire = .ok result) :
    (∃ producer consumer consumed,
      (input.val.wires wire).endpoints = [
        { node := producer, port := .output },
        { node := consumer, port := .free consumed }] ∧
      applyFusionOrdered input wire producer consumer consumed = .ok result) ∨
    (∃ producer consumer consumed,
      (input.val.wires wire).endpoints = [
        { node := consumer, port := .free consumed },
        { node := producer, port := .output }] ∧
      applyFusionOrdered input wire producer consumer consumed = .ok result) := by
  cases hlist : (input.val.wires wire).endpoints with
  | nil => simp [applyFusion, hlist] at happly
  | cons first rest =>
      cases rest with
      | nil => simp [applyFusion, hlist] at happly
      | cons second tail =>
          cases tail with
          | cons third tail => simp [applyFusion, hlist] at happly
          | nil =>
              cases hfirst : first.port <;> cases hsecond : second.port <;>
                simp [applyFusion, hlist, hfirst, hsecond] at happly
              · rename_i consumed
                have hfirstEq : first =
                    { node := first.node, port := Diagram.CPort.output } := by
                  rcases first with ⟨firstNode, firstPort⟩
                  change firstPort = Diagram.CPort.output at hfirst
                  subst firstPort
                  rfl
                have hsecondEq : second =
                    { node := second.node, port := Diagram.CPort.free consumed } := by
                  rcases second with ⟨secondNode, secondPort⟩
                  change secondPort = Diagram.CPort.free consumed at hsecond
                  subst secondPort
                  rfl
                exact Or.inl ⟨first.node, second.node, consumed,
                  by rw [hfirstEq, hsecondEq], happly⟩
              · rename_i consumed
                have hfirstEq : first =
                    { node := first.node, port := Diagram.CPort.free consumed } := by
                  rcases first with ⟨firstNode, firstPort⟩
                  change firstPort = Diagram.CPort.free consumed at hfirst
                  subst firstPort
                  rfl
                have hsecondEq : second =
                    { node := second.node, port := Diagram.CPort.output } := by
                  rcases second with ⟨secondNode, secondPort⟩
                  change secondPort = Diagram.CPort.output at hsecond
                  subst secondPort
                  rfl
                exact Or.inr ⟨second.node, first.node, consumed,
                  by rw [hfirstEq, hsecondEq], happly⟩

theorem applyFusion_realizes
    (happly : applyFusion input wire = .ok result) :
    ∃ producer consumer consumed,
      ((input.val.wires wire).endpoints = [
          { node := producer, port := .output },
          { node := consumer, port := .free consumed }] ∨
        (input.val.wires wire).endpoints = [
          { node := consumer, port := .free consumed },
          { node := producer, port := .output }]) ∧
      ∃ (hdistinct : producer ≠ consumer)
        (consumerRegion : Fin input.val.regionCount)
        (producerPorts : Nat) (producerTerm : Term 0 (Fin producerPorts))
        (consumerPorts : Nat) (consumerTerm : Term 0 (Fin consumerPorts))
        (hport : consumed < consumerPorts)
        (producerWires : Fin producerPorts → Fin input.val.wireCount)
        (consumerWires : Fin consumerPorts → Fin input.val.wireCount),
        result.Realizes
          (fusionRaw input wire producer consumer hdistinct consumerRegion
            producerTerm consumerTerm producerWires consumerWires
            ⟨consumed, hport⟩)
          (fusionWireProvenance input wire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWires
            consumerWires ⟨consumed, hport⟩)
          (fusionInterfaceTransport input wire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWires
            consumerWires ⟨consumed, hport⟩) := by
  rcases applyFusion_success happly with
    ⟨producer, consumer, consumed, hendpoints, hordered⟩ |
      ⟨producer, consumer, consumed, hendpoints, hordered⟩
  · obtain ⟨hdistinct, producerRegion, producerPorts, producerTerm,
      consumerRegion, consumerPorts, consumerTerm, hport, producerWires,
      consumerWires, _, _, _, _, _, hrealizes⟩ :=
        applyFusionOrdered_realizes hordered
    exact ⟨producer, consumer, consumed, Or.inl hendpoints, hdistinct,
      consumerRegion, producerPorts, producerTerm, consumerPorts, consumerTerm,
      hport, producerWires, consumerWires, hrealizes⟩
  · obtain ⟨hdistinct, producerRegion, producerPorts, producerTerm,
      consumerRegion, consumerPorts, consumerTerm, hport, producerWires,
      consumerWires, _, _, _, _, _, hrealizes⟩ :=
        applyFusionOrdered_realizes hordered
    exact ⟨producer, consumer, consumed, Or.inr hendpoints, hdistinct,
      consumerRegion, producerPorts, producerTerm, consumerPorts, consumerTerm,
      hport, producerWires, consumerWires, hrealizes⟩

def subtermAt? : {bound : Nat} → Term bound α →
    List PathSegment → Option (Sigma fun depth => Term depth α)
  | bound, term, [] => some ⟨bound, term⟩
  | _, .lam body, .body :: rest => subtermAt? body rest
  | _, .app fn _, .fn :: rest => subtermAt? fn rest
  | _, .app _ argument, .arg :: rest => subtermAt? argument rest
  | _, _, _ :: _ => none

def lowerToZero : (bound : Nat) → Term bound α → Option (Term 0 α)
  | 0, term => some term
  | bound + 1, term => do
      let lowered ← term.unlift
      lowerToZero bound lowered

def replaceAtPort? : {bound : Nat} → Term bound α →
    List PathSegment → α → Option (Term bound α)
  | _, _, [], replacement => some (.port replacement)
  | _, .lam body, .body :: rest, replacement =>
      (replaceAtPort? body rest replacement).map Term.lam
  | _, .app fn argument, .fn :: rest, replacement =>
      (replaceAtPort? fn rest replacement).map fun replaced =>
        .app replaced argument
  | _, .app fn argument, .arg :: rest, replacement =>
      (replaceAtPort? argument rest replacement).map fun replaced =>
        .app fn replaced
  | _, _, _ :: _, _ => none

private def fissionKeepEndpoint (node : Fin nodes)
    (endpoint : Diagram.CEndpoint nodes) : Bool :=
  if endpoint.node = node then
    match endpoint.port with
    | .free _ => false
    | _ => true
  else true

@[simp] theorem fissionKeepEndpoint_of_node_ne
    (node : Fin nodes) (endpoint : Diagram.CEndpoint nodes)
    (different : endpoint.node ≠ node) :
    fissionKeepEndpoint node endpoint = true := by
  simp [fissionKeepEndpoint, different]

@[simp] theorem fissionKeepEndpoint_output
    (node endpointNode : Fin nodes) :
    fissionKeepEndpoint node
      ({ node := endpointNode, port := Diagram.CPort.output } :
        Diagram.CEndpoint nodes) = true := by
  simp [fissionKeepEndpoint]

def fissionRaw (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (region : Fin input.val.regionCount)
    (producerGlobal : Term 0 (Fin input.val.wireCount))
    (residualGlobal : Term 0 (Option (Fin input.val.wireCount))) :
    Diagram.ConcreteDiagram :=
  let producer := producerGlobal.compact
  let residual := residualGlobal.compact
  { regionCount := input.val.regionCount
    nodeCount := input.val.nodeCount + 1
    wireCount := input.val.wireCount + 1
    root := input.val.root
    regions := input.val.regions
    nodes := Fin.lastCases
      (.term region producerGlobal.freeSupport.length producer)
      (fun candidate =>
        if candidate = node then
          .term region residualGlobal.freeSupport.length residual
        else input.val.nodes candidate)
    wires := Fin.lastCases
      { scope := region
        endpoints :=
          { node := Fin.last input.val.nodeCount, port := Diagram.CPort.output } ::
          (allFin residualGlobal.freeSupport.length).filterMap fun port =>
            if residualGlobal.freeSupport.get port = none then
              some { node := node.castSucc, port := Diagram.CPort.free port }
            else none }
      (fun wire =>
        let original := input.val.wires wire
        { scope := original.scope
          endpoints :=
            (original.endpoints.filter (fissionKeepEndpoint node)).map
                anchoredSplitLiftEndpoint ++
              (allFin producerGlobal.freeSupport.length).filterMap (fun port =>
                if producerGlobal.freeSupport.get port = wire then
                  some {
                    node := Fin.last input.val.nodeCount
                    port := Diagram.CPort.free port
                  }
                else none) ++
              (allFin residualGlobal.freeSupport.length).filterMap (fun port =>
                if residualGlobal.freeSupport.get port = some wire then
                  some { node := node.castSucc, port := Diagram.CPort.free port }
                else none) }) }

def fissionWireProvenance (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (region : Fin input.val.regionCount)
    (producerGlobal : Term 0 (Fin input.val.wireCount))
    (residualGlobal : Term 0 (Option (Fin input.val.wireCount))) :
    WireProvenance input.val
      (fissionRaw input node region producerGlobal residualGlobal) :=
  WireProvenance.append input.val
    (fissionRaw input node region producerGlobal residualGlobal) 1 rfl

def fissionInterfaceTransport (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (region : Fin input.val.regionCount)
    (producerGlobal : Term 0 (Fin input.val.wireCount))
    (residualGlobal : Term 0 (Option (Fin input.val.wireCount))) :
    InterfaceTransport input.val
      (fissionRaw input node region producerGlobal residualGlobal) :=
  InterfaceTransport.append input.val
    (fissionRaw input node region producerGlobal residualGlobal) 1 rfl

def applyFission (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (path : List PathSegment) :
    Except StepError (StepReceipt input) :=
  match input.val.nodes node with
  | .term region freePorts term =>
      match resolveNodeFreeWires? input node freePorts with
      | none => .error .invalidWire
      | some portWire =>
          let global := term.mapFree portWire
          match subtermAt? global path,
              replaceAtPort? (global.mapFree some) path none with
          | some ⟨depth, selected⟩, some residual =>
              match lowerToZero depth selected with
              | none => .error .binderEscape
              | some producer =>
                  match hcheck : Diagram.checkWellFormed signature
                      (fissionRaw input node region producer residual) with
                  | .error error => .error (.resultNotWellFormed error)
                  | .ok result => .ok (StepReceipt.ofChecked input
                      (fissionRaw input node region producer residual)
                      (fissionWireProvenance input node region producer residual)
                      (fissionInterfaceTransport input node region producer
                        residual) result hcheck)
          | _, _ => .error .invalidSelection
  | _ => .error .invalidNode

theorem applyFission_success
    (happly : applyFission input node path = .ok result) :
    ∃ (region : Fin input.val.regionCount) (freePorts : Nat)
      (term : Term 0 (Fin freePorts))
      (portWire : Fin freePorts → Fin input.val.wireCount)
      (depth : Nat) (selected : Term depth (Fin input.val.wireCount))
      (residual : Term 0 (Option (Fin input.val.wireCount)))
      (producer : Term 0 (Fin input.val.wireCount)),
      input.val.nodes node = .term region freePorts term ∧
      resolveNodeFreeWires? input node freePorts = some portWire ∧
      subtermAt? (term.mapFree portWire) path = some ⟨depth, selected⟩ ∧
      replaceAtPort? ((term.mapFree portWire).mapFree some) path none =
        some residual ∧
      lowerToZero depth selected = some producer ∧
      result.result.val = fissionRaw input node region producer residual := by
  unfold applyFission at happly
  split at happly <;> try contradiction
  rename_i region freePorts term hnode
  split at happly <;> try contradiction
  rename_i portWire hportWire
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i depth selected residual hselected hresidual
  split at happly <;> try contradiction
  rename_i producer hproducer
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨region, freePorts, term, portWire, depth, selected, residual,
    producer, hnode, hportWire, hselected, hresidual, hproducer,
    Diagram.checkWellFormed_preserves_input hcheck⟩

theorem applyFission_realizes
    (happly : applyFission input node path = .ok result) :
    ∃ (region : Fin input.val.regionCount) (freePorts : Nat)
      (term : Term 0 (Fin freePorts))
      (portWire : Fin freePorts → Fin input.val.wireCount)
      (depth : Nat) (selected : Term depth (Fin input.val.wireCount))
      (residual : Term 0 (Option (Fin input.val.wireCount)))
      (producer : Term 0 (Fin input.val.wireCount)),
      input.val.nodes node = .term region freePorts term ∧
      resolveNodeFreeWires? input node freePorts = some portWire ∧
      subtermAt? (term.mapFree portWire) path = some ⟨depth, selected⟩ ∧
      replaceAtPort? ((term.mapFree portWire).mapFree some) path none =
        some residual ∧
      lowerToZero depth selected = some producer ∧
      result.Realizes (fissionRaw input node region producer residual)
        (fissionWireProvenance input node region producer residual)
        (fissionInterfaceTransport input node region producer residual) := by
  unfold applyFission at happly
  split at happly <;> try contradiction
  rename_i region freePorts term hnode
  split at happly <;> try contradiction
  rename_i portWire hportWire
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i depth selected residual hselected hresidual
  split at happly <;> try contradiction
  rename_i producer hproducer
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨region, freePorts, term, portWire, depth, selected, residual,
    producer, hnode, hportWire, hselected, hresidual, hproducer,
    StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

def ConversionPayload.freshPorts
    (payload : ConversionPayload input node) :
    List (Fin payload.newFreePorts) :=
  (allFin payload.newFreePorts).filter fun port =>
    (payload.existingWire? port).isNone

private def conversionKeepsEndpoint
    (node : Fin nodes) (endpoint : Diagram.CEndpoint nodes) : Bool :=
  if endpoint.node = node then
    match endpoint.port with
    | .free _ => false
    | _ => true
  else
    true

def conversionRaw (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node) : Diagram.ConcreteDiagram where
  regionCount := input.val.regionCount
  nodeCount := input.val.nodeCount
  wireCount := input.val.wireCount + payload.freshPorts.length
  root := input.val.root
  regions := input.val.regions
  nodes := fun candidate =>
    if candidate = node then
      .term payload.region payload.newFreePorts payload.newTerm
    else
      input.val.nodes candidate
  wires := Fin.addCases
    (fun wire =>
      let original := input.val.wires wire
      {
        scope := original.scope
        endpoints :=
          original.endpoints.filter (conversionKeepsEndpoint node) ++
            (allFin payload.newFreePorts).filterMap fun port =>
              if payload.existingWire? port = some wire then
                some { node := node, port := .free port }
              else
                none
      })
    (fun fresh =>
      {
        scope := payload.region
        endpoints := [{
          node := node
          port := .free (payload.freshPorts.get fresh)
        }]
      })

def conversionWireProvenance (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node) :
    WireProvenance input.val (conversionRaw input node payload) :=
  WireProvenance.append input.val (conversionRaw input node payload)
    payload.freshPorts.length rfl

def conversionInterfaceTransport (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node) :
    InterfaceTransport input.val (conversionRaw input node payload) :=
  InterfaceTransport.append input.val (conversionRaw input node payload)
    payload.freshPorts.length rfl

def applyConversion (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node) :
    Except StepError (StepReceipt input) :=
  match hcheck : Diagram.checkWellFormed signature
      (conversionRaw input node payload) with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (StepReceipt.ofChecked input
      (conversionRaw input node payload)
      (conversionWireProvenance input node payload)
      (conversionInterfaceTransport input node payload) result hcheck)

theorem applyConversion_preserves_raw
    (happly : applyConversion input node payload = .ok result) :
    result.result.val = conversionRaw input node payload := by
  unfold applyConversion at happly
  split at happly
  · contradiction
  · rename_i checked hcheck
    cases happly
    exact Diagram.checkWellFormed_preserves_input hcheck

theorem applyConversion_realizes
    (happly : applyConversion input node payload = .ok result) :
    result.Realizes (conversionRaw input node payload)
      (conversionWireProvenance input node payload)
      (conversionInterfaceTransport input node payload) := by
  unfold applyConversion at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

theorem CongruencePayload.betaEta
    (payload : CongruencePayload input first second) :
    BetaEta (payload.firstTerm.mapFree payload.firstPort)
      (payload.secondTerm.mapFree payload.secondPort) :=
  checkCertificate_sound payload.certificate_valid

theorem CongruencePayload.eval_eq
    (payload : CongruencePayload input first second)
    (model : LambdaModel)
    (environment : Fin payload.commonPorts → model.Carrier) :
    model.eval payload.firstTerm (environment ∘ payload.firstPort) =
      model.eval payload.secondTerm (environment ∘ payload.secondPort) := by
  rw [← model.eval_mapFree, ← model.eval_mapFree]
  exact model.betaEta_sound payload.betaEta

structure CongruenceJoinPlan (input : Diagram.CheckedDiagram signature) where
  raw : Diagram.ConcreteDiagram
  provenance : WireProvenance input.val raw
  interface : InterfaceTransport input.val raw

def congruenceJoinPlan (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second) :
    CongruenceJoinPlan input :=
  if input.val.Encloses (input.val.wires payload.firstOutput).scope
      (input.val.wires payload.secondOutput).scope then
    {
      raw := joinWireRaw input.val payload.firstOutput payload.secondOutput
      provenance :=
        joinWireProvenance input.val payload.firstOutput payload.secondOutput
      interface :=
        joinWireInterfaceTransport input.val payload.firstOutput
          payload.secondOutput
    }
  else
    {
      raw := joinWireRaw input.val payload.secondOutput payload.firstOutput
      provenance :=
        joinWireProvenance input.val payload.secondOutput payload.firstOutput
      interface :=
        joinWireInterfaceTransport input.val payload.secondOutput
          payload.firstOutput
    }

def congruenceJoinRaw (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second) : Diagram.ConcreteDiagram :=
  (congruenceJoinPlan input payload).raw

def congruenceJoinWireProvenance (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second) :
    WireProvenance input.val (congruenceJoinRaw input payload) :=
  (congruenceJoinPlan input payload).provenance

/-- Logical transport follows the same enclosing-wire choice as the concrete
join, but maps the absorbed output identity to the retained output identity. -/
def congruenceJoinInterfaceTransport
    (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second) :
    InterfaceTransport input.val (congruenceJoinRaw input payload) :=
  (congruenceJoinPlan input payload).interface

def applyCongruenceJoin (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second) :
    Except StepError (StepReceipt input) :=
  match hcheck : Diagram.checkWellFormed signature
      (congruenceJoinRaw input payload) with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (StepReceipt.ofChecked input
      (congruenceJoinRaw input payload)
      (congruenceJoinWireProvenance input payload)
      (congruenceJoinInterfaceTransport input payload) result hcheck)

theorem applyCongruenceJoin_preserves_raw
    (happly : applyCongruenceJoin input payload = .ok result) :
    result.result.val = congruenceJoinRaw input payload := by
  unfold applyCongruenceJoin at happly
  split at happly
  · contradiction
  · rename_i checked hcheck
    cases happly
    exact Diagram.checkWellFormed_preserves_input hcheck

theorem applyCongruenceJoin_realizes
    (happly : applyCongruenceJoin input payload = .ok result) :
    result.Realizes (congruenceJoinRaw input payload)
      (congruenceJoinWireProvenance input payload)
      (congruenceJoinInterfaceTransport input payload) := by
  unfold applyCongruenceJoin at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

/-- Closed-term introduction is the canonical spawn specialization with no
free ports and one fresh output wire. -/
def closedTermIntroRaw (input : Diagram.ConcreteDiagram)
    (region : Fin input.regionCount) (term : Term 0 (Fin 0)) :
    Diagram.ConcreteDiagram :=
  spawnNodeRaw input (.term region 0 term) region 1 (fun _ => .output)

def closedTermIntroWireProvenance (input : Diagram.ConcreteDiagram)
    (region : Fin input.regionCount) (term : Term 0 (Fin 0)) :
    WireProvenance input (closedTermIntroRaw input region term) :=
  spawnNodeWireProvenance input (.term region 0 term) region 1
    (fun _ => .output)

def closedTermIntroInterfaceTransport (input : Diagram.ConcreteDiagram)
    (region : Fin input.regionCount) (term : Term 0 (Fin 0)) :
    InterfaceTransport input (closedTermIntroRaw input region term) :=
  spawnNodeInterfaceTransport input (.term region 0 term) region 1
    (fun _ => .output)

def applyClosedTermIntro (input : Diagram.CheckedDiagram signature)
    (region : Fin input.val.regionCount) (term : Term 0 (Fin 0)) :
    Except StepError (StepReceipt input) :=
  match hcheck : Diagram.checkWellFormed signature
      (closedTermIntroRaw input.val region term) with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (StepReceipt.ofChecked input
      (closedTermIntroRaw input.val region term)
      (closedTermIntroWireProvenance input.val region term)
      (closedTermIntroInterfaceTransport input.val region term) result hcheck)

theorem applyClosedTermIntro_preserves_raw
    (happly : applyClosedTermIntro input region term = .ok result) :
    result.result.val = closedTermIntroRaw input.val region term := by
  unfold applyClosedTermIntro at happly
  split at happly
  · contradiction
  · rename_i checked hcheck
    cases happly
    exact Diagram.checkWellFormed_preserves_input hcheck

theorem applyClosedTermIntro_realizes
    (happly : applyClosedTermIntro input region term = .ok result) :
    result.Realizes (closedTermIntroRaw input.val region term)
      (closedTermIntroWireProvenance input.val region term)
      (closedTermIntroInterfaceTransport input.val region term) := by
  unfold applyClosedTermIntro at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

/-- The appended zero-port term occurrence is satisfied whenever its output
lookup carries the closed term's denotation. -/
private theorem closedTermIntro_freshOccurrence_denotes
    (input : Diagram.ConcreteDiagram)
    (scope : Fin input.regionCount) (term : Term 0 (Fin 0))
    (context : Diagram.ConcreteElaboration.WireContext
      (closedTermIntroRaw input scope term))
    (binders : Diagram.ConcreteElaboration.BinderContext
      (closedTermIntroRaw input scope term) rels)
    (recurse : ∀ {currentRels : Theory.RelCtx},
      (region : Fin input.regionCount) →
      (currentContext : Diagram.ConcreteElaboration.WireContext
        (closedTermIntroRaw input scope term)) →
      Diagram.ConcreteElaboration.BinderContext
        (closedTermIntroRaw input scope term) currentRels →
      Option (Diagram.Region signature currentContext.length currentRels))
    (freshItems : Diagram.ItemSeq signature context.length rels)
    (hcompile : Diagram.ConcreteElaboration.compileOccurrencesWith? signature
      (closedTermIntroRaw input scope term) recurse context binders
      [Diagram.ConcreteElaboration.LocalOccurrence.node
        (regions := input.regionCount) (Fin.last input.nodeCount)] =
        some freshItems)
    (model : LambdaModel)
    (named : Diagram.NamedEnv model.Carrier signature)
    (rawEnv : Fin context.length → model.Carrier)
    (relEnv : Diagram.RelEnv model.Carrier rels)
    (houtput : ∀ output,
      Diagram.ConcreteElaboration.resolvePort?
        (closedTermIntroRaw input scope term) context
        (Fin.last input.nodeCount) .output = some output →
      rawEnv output = model.eval term Fin.elim0) :
    Diagram.denoteItemSeq model named rawEnv relEnv freshItems := by
  simp only [Diagram.ConcreteElaboration.compileOccurrencesWith?,
    Diagram.ConcreteElaboration.compileOccurrenceWith?] at hcompile
  unfold Diagram.ConcreteElaboration.compileNode? at hcompile
  simp only [closedTermIntroRaw, spawnNodeRaw_newNode] at hcompile
  cases hresolved : Diagram.ConcreteElaboration.resolvePort?
      (closedTermIntroRaw input scope term) context
      (Fin.last input.nodeCount) .output with
  | none =>
      have hresolved' : Diagram.ConcreteElaboration.resolvePort?
          (spawnNodeRaw input (.term scope 0 term) scope 1 (fun _ => .output))
          context (Fin.last input.nodeCount) .output = none := by
        simpa only [closedTermIntroRaw] using hresolved
      simp [hresolved'] at hcompile
  | some output =>
      have hresolved' : Diagram.ConcreteElaboration.resolvePort?
          (spawnNodeRaw input (.term scope 0 term) scope 1 (fun _ => .output))
          context (Fin.last input.nodeCount) .output = some output := by
        simpa only [closedTermIntroRaw] using hresolved
      simp only [hresolved', Option.bind_some] at hcompile
      cases hfree : Diagram.ConcreteElaboration.resolvePorts?
          (closedTermIntroRaw input scope term) context
          (Fin.last input.nodeCount) 0 (fun index => .free index) with
      | none =>
          have hfree' : Diagram.ConcreteElaboration.resolvePorts?
              (spawnNodeRaw input (.term scope 0 term) scope 1
                (fun _ => .output)) context
              (Fin.last input.nodeCount) 0 (fun index => .free index) = none := by
            simpa only [closedTermIntroRaw] using hfree
          simp [hfree'] at hcompile
      | some free =>
          have hfree' : Diagram.ConcreteElaboration.resolvePorts?
              (spawnNodeRaw input (.term scope 0 term) scope 1
                (fun _ => .output)) context
              (Fin.last input.nodeCount) 0 (fun index => .free index) =
                some free := by
            simpa only [closedTermIntroRaw] using hfree
          simp only [hfree'] at hcompile
          change some (Diagram.ItemSeq.cons
            (Diagram.Item.equation output (term.mapFree free))
            Diagram.ItemSeq.nil) = some freshItems at hcompile
          injection hcompile with hitems
          rw [← hitems]
          simp only [Diagram.denoteItemSeq_cons, Diagram.denoteItem_equation,
            Diagram.denoteItemSeq_nil, and_true]
          have hfreeEq : free = Fin.elim0 := by
            funext index
            exact Fin.elim0 index
          rw [hfreeEq]
          rw [model.eval_mapFree]
          have henvEq : rawEnv ∘ Fin.elim0 = Fin.elim0 := by
            funext index
            exact Fin.elim0 index
          rw [henvEq]
          exact houtput output hresolved

/-- Closed-term introduction supplies the reverse semantic witness at a
nested spawn site. -/
theorem closedTermIntro_regionSiteReflection
    (input : ConcreteDiagram) (scope : Fin input.regionCount)
    (term : Term 0 (Fin 0))
    (hinput : input.WellFormed signature)
    (htarget : (closedTermIntroRaw input scope term).WellFormed signature) :
    SpawnRegionSiteReflection (signature := signature) input
      (.term scope 0 term) scope 1 (fun _ => .output) := by
  intro rels fuel source target embedding binders hsourceExact htargetExact
    sourceBody targetBody hsourceBody htargetBody model named outerEnv relEnv
    hsourceDenotes
  let sourceNodes :=
    (filterFin fun old => decide ((input.nodes old).region = scope)).map
      (fun old => ConcreteElaboration.LocalOccurrence.node
        (regions := input.regionCount) old)
  let sourceChildren :=
    (filterFin fun child =>
      decide ((input.regions child).parent? = some scope)).map
      (ConcreteElaboration.LocalOccurrence.child (nodes := input.nodeCount))
  let targetNodes := sourceNodes.map (spawnNodeRaw_oldOccurrence input)
  let targetChildren := sourceChildren.map (spawnNodeRaw_oldOccurrence input)
  let fresh := [ConcreteElaboration.LocalOccurrence.node
    (regions := input.regionCount) (Fin.last input.nodeCount)]
  have hsourceOccurrences :
      ConcreteElaboration.localOccurrences input scope =
        sourceNodes ++ sourceChildren := by rfl
  have htargetOccurrences :
      ConcreteElaboration.localOccurrences
          (closedTermIntroRaw input scope term) scope =
        targetNodes ++ fresh ++ targetChildren := by
    change ConcreteElaboration.localOccurrences
      (spawnNodeRaw input (.term scope 0 term) scope 1 (fun _ => .output))
      scope = _
    rw [spawnNodeRaw_localOccurrences]
    rw [if_pos (by rfl)]
    simp only [sourceNodes, sourceChildren, targetNodes, targetChildren, fresh,
      List.map_map]
    rfl
  simp only [ConcreteElaboration.compileRegion?] at hsourceBody htargetBody
  cases hsourceItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
      input (ConcreteElaboration.compileRegion? signature input fuel)
      (source.extend scope) binders
      (ConcreteElaboration.localOccurrences input scope) with
  | none => simp [hsourceItemsEq] at hsourceBody
  | some sourceItems =>
    simp [hsourceItemsEq] at hsourceBody
    subst sourceBody
    cases htargetItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input (.term scope 0 term) scope 1 (fun _ => .output))
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input (.term scope 0 term) scope 1
            (fun _ => .output)) fuel)
        (target.extend scope) binders
        (ConcreteElaboration.localOccurrences
          (spawnNodeRaw input (.term scope 0 term) scope 1
            (fun _ => .output)) scope) with
    | none => simp [htargetItemsEq] at htargetBody
    | some targetItems =>
      simp [htargetItemsEq] at htargetBody
      subst targetBody
      have htargetOrdered :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input (.term scope 0 term) scope 1
                (fun _ => .output))
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input (.term scope 0 term) scope 1
                  (fun _ => .output)) fuel)
              (target.extend scope) binders
              (targetNodes ++ (fresh ++ targetChildren)) =
            some targetItems := by
        rw [← List.append_assoc, ← htargetOccurrences]
        exact htargetItemsEq
      obtain ⟨nodeItems, restItems, hnodeItems, hrestItems,
          htargetItems⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input (.term scope 0 term) scope 1
              (fun _ => .output)) fuel)
          (target.extend scope) binders targetNodes
          (fresh ++ targetChildren) targetItems htargetOrdered
      obtain ⟨freshItems, childItems, hfreshItems, hchildItems,
          hrestItemsEq⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input (.term scope 0 term) scope 1
              (fun _ => .output)) fuel)
          (target.extend scope) binders fresh targetChildren restItems hrestItems
      have holdCompile :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input (.term scope 0 term) scope 1
                (fun _ => .output))
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input (.term scope 0 term) scope 1
                  (fun _ => .output)) fuel)
              (target.extend scope) binders
              ((ConcreteElaboration.localOccurrences input scope).map
                (spawnNodeRaw_oldOccurrence input)) =
            some (nodeItems.append childItems) := by
        rw [hsourceOccurrences, List.map_append]
        change ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input (.term scope 0 term) scope 1
              (fun _ => .output))
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input (.term scope 0 term) scope 1
                (fun _ => .output)) fuel)
            (target.extend scope) binders (targetNodes ++ targetChildren) = _
        exact ConcreteElaboration.compileOccurrencesWith?_append
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input (.term scope 0 term) scope 1
              (fun _ => .output)) fuel)
          (target.extend scope) binders targetNodes targetChildren nodeItems
          childItems hnodeItems hchildItems
      have holdMap := spawnNodeRaw_compileOldOccurrencesAtSite input
        (.term scope 0 term) scope 1 (fun _ => .output) hinput htarget rfl fuel
        source target embedding binders hsourceExact htargetExact
      rw [hsourceItemsEq] at holdMap
      simp only [Option.map_some] at holdMap
      rw [holdCompile] at holdMap
      have holdItems : nodeItems.append childItems =
          sourceItems.renameWires (embedding.extend scope).index :=
        Option.some.inj holdMap
      refine spawnNodeRaw_finishRegion_site_reflects input
        (.term scope 0 term) scope 1 (fun _ => .output) source target embedding
        htargetExact.nodup sourceItems targetItems model named outerEnv relEnv
        (fun _ => model.eval term Fin.elim0) ?_ hsourceDenotes
      intro rawEnv hfresh holdDenotes
      rw [← holdItems] at holdDenotes
      rw [denoteItemSeq_append] at holdDenotes
      rcases holdDenotes with ⟨hnodeDenotes, hchildDenotes⟩
      have hfreshDenotes := closedTermIntro_freshOccurrence_denotes input scope
        term (target.extend scope) binders
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input (.term scope 0 term) scope 1
            (fun _ => .output)) fuel)
        freshItems hfreshItems model named rawEnv relEnv
      have hfreshHolds : denoteItemSeq model named rawEnv relEnv freshItems := by
        apply hfreshDenotes
        intro output hresolve
        obtain ⟨wire, hoccurs, hget⟩ :=
          ConcreteElaboration.resolvePort?_sound hresolve
        have hwire : wire = Fin.natAdd input.wireCount (0 : Fin 1) := by
          apply ConcreteElaboration.endpoint_wire_unique
            htarget.wire_endpoints_are_disjoint hoccurs
          unfold ConcreteDiagram.EndpointOccurs
          simp only [closedTermIntroRaw, spawnNodeRaw, Fin.addCases_right]
          change (⟨Fin.last input.nodeCount, CPort.output⟩ :
            CEndpoint (input.nodeCount + 1)) ∈
              [⟨Fin.last input.nodeCount, CPort.output⟩]
          exact List.mem_singleton.mpr rfl
        have hgetFresh : (target.extend scope).get output =
            Fin.natAdd input.wireCount (0 : Fin 1) := hget.trans hwire
        have hindex : output = spawnNodeRaw_freshExtendedIndex input
            (.term scope 0 term) scope 1 (fun _ => .output) target 0 := by
          have hfreshMem : Fin.natAdd input.wireCount (0 : Fin 1) ∈
              target.extend scope := by
            rw [← hgetFresh]
            exact List.get_mem (target.extend scope) output
          obtain ⟨found, hfound⟩ :=
            ConcreteElaboration.WireContext.lookup?_complete
              hfreshMem
          have houtputFound := ConcreteElaboration.WireContext.lookup?_unique
            (context := target.extend scope) htargetExact.nodup hfound
            (other := output) hgetFresh
          have hfreshFound := ConcreteElaboration.WireContext.lookup?_unique
            (context := target.extend scope) htargetExact.nodup hfound
            (other := spawnNodeRaw_freshExtendedIndex input
              (.term scope 0 term) scope 1 (fun _ => .output) target 0)
              (spawnNodeRaw_freshExtendedIndex_get input
                (.term scope 0 term) scope 1 (fun _ => .output) target 0)
          exact houtputFound.trans hfreshFound.symm
        rw [hindex]
        exact hfresh 0
      rw [htargetItems, hrestItemsEq]
      rw [denoteItemSeq_append]
      exact ⟨hnodeDenotes,
        (denoteItemSeq_append model named rawEnv relEnv freshItems childItems).2
          ⟨hfreshHolds, hchildDenotes⟩⟩

/-- Closed-term introduction supplies the fresh hidden witness when its site
is the open root sheet. -/
theorem closedTermIntro_rootSiteReflection
    (source : CheckedOpenDiagram signature)
    (scope : Fin source.val.diagram.regionCount) (term : Term 0 (Fin 0))
    (hroot : source.val.diagram.root = scope)
    (htarget : (closedTermIntroRaw source.val.diagram scope term).WellFormed
      signature) :
    SpawnRootSiteReflection source (.term scope 0 term) scope 1
      (fun _ => .output) := by
  intro sourceBody targetBody hsourceBody htargetBody model named outerEnv
    hsourceDenotes
  let input := source.val.diagram
  let targetOpen := spawnNodeRawOpen source.val (.term scope 0 term) scope 1
    (fun _ => .output)
  let sourceNodes :=
    (filterFin fun old => decide ((input.nodes old).region = input.root)).map
      (fun old => ConcreteElaboration.LocalOccurrence.node
        (regions := input.regionCount) old)
  let sourceChildren :=
    (filterFin fun child =>
      decide ((input.regions child).parent? = some input.root)).map
      (ConcreteElaboration.LocalOccurrence.child (nodes := input.nodeCount))
  let targetNodes := sourceNodes.map (spawnNodeRaw_oldOccurrence input)
  let targetChildren := sourceChildren.map (spawnNodeRaw_oldOccurrence input)
  let fresh := [ConcreteElaboration.LocalOccurrence.node
    (regions := input.regionCount) (Fin.last input.nodeCount)]
  have hsourceOccurrences :
      ConcreteElaboration.localOccurrences input input.root =
        sourceNodes ++ sourceChildren := by rfl
  have htargetOccurrences :
      ConcreteElaboration.localOccurrences targetOpen.diagram input.root =
        targetNodes ++ fresh ++ targetChildren := by
    change ConcreteElaboration.localOccurrences
      (spawnNodeRaw input (.term scope 0 term) scope 1 (fun _ => .output))
      input.root = _
    rw [spawnNodeRaw_localOccurrences, if_pos (by simpa using hroot.symm)]
    simp only [input, sourceNodes, sourceChildren, targetNodes,
      targetChildren, fresh, List.map_map]
    rfl
  change ConcreteElaboration.compileRoot? signature input
      source.val.exposedWires source.val.hiddenWires = some sourceBody
    at hsourceBody
  change ConcreteElaboration.compileRoot? signature targetOpen.diagram
      targetOpen.exposedWires targetOpen.hiddenWires = some targetBody
    at htargetBody
  simp only [ConcreteElaboration.compileRoot?] at hsourceBody htargetBody
  cases hsourceItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
      input (ConcreteElaboration.compileRegion? signature input input.regionCount)
      (source.val.exposedWires ++ source.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input input.root) with
  | none => simp [hsourceItemsEq] at hsourceBody
  | some sourceItems =>
    simp [hsourceItemsEq] at hsourceBody
    subst sourceBody
    cases htargetItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
        targetOpen.diagram
        (ConcreteElaboration.compileRegion? signature targetOpen.diagram
          targetOpen.diagram.regionCount)
        (targetOpen.exposedWires ++ targetOpen.hiddenWires)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences targetOpen.diagram
          targetOpen.diagram.root) with
    | none => simp [input, targetOpen, htargetItemsEq] at htargetBody
    | some targetItems =>
      simp [input, targetOpen, htargetItemsEq] at htargetBody
      subst targetBody
      have htargetOrdered :
          ConcreteElaboration.compileOccurrencesWith? signature
              targetOpen.diagram
              (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                input.regionCount)
              targetOpen.rootWires ConcreteElaboration.BinderContext.empty
              (targetNodes ++ (fresh ++ targetChildren)) = some targetItems := by
        rw [← List.append_assoc, ← htargetOccurrences]
        exact htargetItemsEq
      obtain ⟨nodeItems, restItems, hnodeItems, hrestItems,
          htargetItems⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature targetOpen.diagram
            input.regionCount)
          targetOpen.rootWires ConcreteElaboration.BinderContext.empty
          targetNodes (fresh ++ targetChildren) targetItems htargetOrdered
      obtain ⟨freshItems, childItems, hfreshItems, hchildItems,
          hrestItemsEq⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature targetOpen.diagram
            input.regionCount)
          targetOpen.rootWires ConcreteElaboration.BinderContext.empty
          fresh targetChildren restItems hrestItems
      have holdCompile :
          ConcreteElaboration.compileOccurrencesWith? signature
              targetOpen.diagram
              (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                input.regionCount)
              targetOpen.rootWires ConcreteElaboration.BinderContext.empty
              ((ConcreteElaboration.localOccurrences input input.root).map
                (spawnNodeRaw_oldOccurrence input)) =
            some (nodeItems.append childItems) := by
        rw [hsourceOccurrences, List.map_append]
        change ConcreteElaboration.compileOccurrencesWith? signature
            targetOpen.diagram
            (ConcreteElaboration.compileRegion? signature targetOpen.diagram
              input.regionCount)
            targetOpen.rootWires ConcreteElaboration.BinderContext.empty
            (targetNodes ++ targetChildren) = _
        exact ConcreteElaboration.compileOccurrencesWith?_append
          (ConcreteElaboration.compileRegion? signature targetOpen.diagram
            input.regionCount)
          targetOpen.rootWires ConcreteElaboration.BinderContext.empty
          targetNodes targetChildren nodeItems childItems hnodeItems hchildItems
      let embedding := spawnNodeRawOpenRootEmbedding source.val
        (.term scope 0 term) scope 1 (fun _ => .output) hroot
      have holdMap := spawnNodeRaw_compileOldOccurrencesAtRoot input
        (.term scope 0 term) scope 1 (fun _ => .output)
        source.property.diagram_well_formed htarget rfl hroot input.regionCount
        source.val.rootWires targetOpen.rootWires embedding
        ConcreteElaboration.BinderContext.empty
        (OpenConcreteDiagram.rootWires_exact source.val source.property)
        (OpenConcreteDiagram.rootWires_exact targetOpen
          (spawnNodeRawOpen_wellFormed source (.term scope 0 term) scope 1
            (fun _ => .output) htarget))
      have hsourceItemsRoot :
          ConcreteElaboration.compileOccurrencesWith? signature input
              (ConcreteElaboration.compileRegion? signature input
                input.regionCount)
              source.val.rootWires ConcreteElaboration.BinderContext.empty
              (ConcreteElaboration.localOccurrences input input.root) =
            some sourceItems := by
        exact hsourceItemsEq
      rw [hsourceItemsRoot] at holdMap
      have hmapped : some (nodeItems.append childItems) =
          Option.map (ItemSeq.renameWires embedding.index) (some sourceItems) :=
        holdCompile.symm.trans holdMap
      have holdItems : nodeItems.append childItems =
          sourceItems.renameWires embedding.index := Option.some.inj hmapped
      refine spawnNodeRaw_finishRoot_site_reflects source.val
        (.term scope 0 term) scope 1 (fun _ => .output) hroot sourceItems
        targetItems model named outerEnv (fun _ => model.eval term Fin.elim0)
        ?_ hsourceDenotes
      intro rawEnv hfresh holdDenotes
      have holdItemsExplicit : nodeItems.append childItems =
          sourceItems.renameWires
            (spawnNodeRawOpenRootEmbedding source.val (.term scope 0 term)
              scope 1 (fun _ => .output) hroot).index := by
        exact holdItems
      have holdDenotesExplicit : denoteItemSeq (relCtx := []) model named rawEnv
          PUnit.unit (nodeItems.append childItems) :=
        (congrArg (fun items => denoteItemSeq (relCtx := []) model named rawEnv
          PUnit.unit items) holdItemsExplicit).mpr holdDenotes
      rw [denoteItemSeq_append] at holdDenotesExplicit
      rcases holdDenotesExplicit with ⟨hnodeDenotes, hchildDenotes⟩
      have hfreshDenotes := closedTermIntro_freshOccurrence_denotes input scope
        term targetOpen.rootWires ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.compileRegion? signature targetOpen.diagram
          input.regionCount) freshItems hfreshItems model named rawEnv PUnit.unit
      have hfreshHolds : denoteItemSeq (relCtx := []) model named rawEnv
          PUnit.unit freshItems := by
        apply hfreshDenotes
        intro output hresolve
        obtain ⟨wire, hoccurs, hget⟩ :=
          ConcreteElaboration.resolvePort?_sound hresolve
        have hwire : wire = Fin.natAdd source.val.diagram.wireCount
            (0 : Fin 1) := by
          apply ConcreteElaboration.endpoint_wire_unique
            htarget.wire_endpoints_are_disjoint hoccurs
          dsimp only [input]
          unfold ConcreteDiagram.EndpointOccurs
          simp only [closedTermIntroRaw, spawnNodeRaw, Fin.addCases_right]
          change (⟨Fin.last source.val.diagram.nodeCount, CPort.output⟩ :
            CEndpoint (source.val.diagram.nodeCount + 1)) ∈
              [⟨Fin.last source.val.diagram.nodeCount, CPort.output⟩]
          exact List.mem_singleton.mpr rfl
        have hgetFresh : targetOpen.rootWires.get output =
            Fin.natAdd source.val.diagram.wireCount (0 : Fin 1) :=
          hget.trans hwire
        have hfreshMem : Fin.natAdd source.val.diagram.wireCount (0 : Fin 1) ∈
            targetOpen.rootWires := by
          rw [← hgetFresh]
          exact List.get_mem targetOpen.rootWires output
        obtain ⟨found, hfound⟩ :=
          ConcreteElaboration.WireContext.lookup?_complete hfreshMem
        have houtputFound := ConcreteElaboration.WireContext.lookup?_unique
          (OpenConcreteDiagram.rootWires_exact targetOpen
            (spawnNodeRawOpen_wellFormed source (.term scope 0 term) scope 1
              (fun _ => .output) htarget)).nodup hfound
          (other := output) hgetFresh
        have hfreshFound := ConcreteElaboration.WireContext.lookup?_unique
          (OpenConcreteDiagram.rootWires_exact targetOpen
            (spawnNodeRawOpen_wellFormed source (.term scope 0 term) scope 1
              (fun _ => .output) htarget)).nodup hfound
          (other := spawnNodeRawOpenFreshRootIndex source.val
            (.term scope 0 term) scope 1 (fun _ => .output) hroot 0)
          (spawnNodeRawOpenFreshRootIndex_get source.val (.term scope 0 term)
            scope 1 (fun _ => .output) hroot 0)
        rw [houtputFound.trans hfreshFound.symm]
        exact hfresh 0
      rw [htargetItems, hrestItemsEq, denoteItemSeq_append]
      exact ⟨hnodeDenotes,
        (denoteItemSeq_append (relCtx := []) model named rawEnv PUnit.unit
          freshItems childItems).2 ⟨hfreshHolds, hchildDenotes⟩⟩

/-- Ordered checked-open semantics is invariant under closed-term
introduction at every routed site and cut parity. -/
theorem closedTermIntroOpen_equiv
    (source : CheckedOpenDiagram signature)
    (scope : Fin source.val.diagram.regionCount) (term : Term 0 (Fin 0))
    (htarget : (closedTermIntroRaw source.val.diagram scope term).WellFormed
      signature)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth)
    (model : LambdaModel) (named : NamedEnv model.Carrier signature)
    (args : Fin source.val.boundary.length → model.Carrier) :
    let targetOpen := spawnNodeRawOpen source.val (.term scope 0 term) scope 1
      (fun _ => .output)
    let targetWf := spawnNodeRawOpen_wellFormed source (.term scope 0 term)
      scope 1 (fun _ => .output) htarget
    let boundaryLength : targetOpen.boundary.length = source.val.boundary.length :=
      by simp [targetOpen, spawnNodeRawOpen]
    source.denote model named args ↔
      targetOpen.denote targetWf model named
        (args ∘ Fin.cast boundaryLength) := by
  dsimp only
  have hregionReflect : SpawnRegionSiteReflection (signature := signature)
      source.val.diagram (.term scope 0 term) scope 1 (fun _ => .output) :=
    closedTermIntro_regionSiteReflection source.val.diagram scope term
      source.property.diagram_well_formed htarget
  have hrootReflect : SpawnRootSiteReflectionAtRoot source
      (.term scope 0 term) scope 1 (fun _ => .output) := by
    intro hroot
    exact closedTermIntro_rootSiteReflection source scope term hroot htarget
  have hprojects := spawnNodeRawOpen_projects source (.term scope 0 term)
    scope 1 (fun _ => .output) rfl htarget route hdepth model named args
  have hreflects := spawnNodeRawOpen_reflects source (.term scope 0 term)
    scope 1 (fun _ => .output) rfl htarget hrootReflect hregionReflect route
    hdepth model named args
  by_cases heven : depth % 2 = 0
  · exact ⟨hreflects.1 heven, hprojects.1 heven⟩
  · have hodd : depth % 2 = 1 := by omega
    exact ⟨hprojects.2 hodd, hreflects.2 hodd⟩

theorem ConversionPayload.betaEta
    (payload : ConversionPayload input node) :
    BetaEta (payload.oldTerm.mapFree payload.oldPort)
      (payload.newTerm.mapFree payload.newPort) :=
  checkCertificate_sound payload.certificate_valid

theorem ConversionPayload.eval_eq
    (payload : ConversionPayload input node)
    (model : LambdaModel)
    (environment : Fin payload.commonPorts → model.Carrier) :
    model.eval payload.oldTerm (environment ∘ payload.oldPort) =
      model.eval payload.newTerm (environment ∘ payload.newPort) := by
  rw [← model.eval_mapFree, ← model.eval_mapFree]
  exact model.betaEta_sound payload.betaEta

theorem ConversionPayload.exists_common_environment
    (payload : ConversionPayload input node)
    (oldValue : Fin payload.oldFreePorts → D)
    (newValue : Fin payload.newFreePorts → D)
    (aligned : ∀ old new,
      payload.oldPort old = payload.newPort new →
        oldValue old = newValue new) :
    ∃ environment : Fin payload.commonPorts → D,
      environment ∘ payload.oldPort = oldValue ∧
        environment ∘ payload.newPort = newValue :=
  exists_commonPort_environment payload.oldPort payload.newPort
    payload.oldPort_injective payload.newPort_injective
    payload.commonPorts_covered oldValue newValue aligned

theorem CongruencePayload.exists_common_environment
    (payload : CongruencePayload input first second)
    (firstValue : Fin payload.firstFreePorts → D)
    (secondValue : Fin payload.secondFreePorts → D)
    (aligned : ∀ left right,
      payload.firstPort left = payload.secondPort right →
        firstValue left = secondValue right) :
    ∃ environment : Fin payload.commonPorts → D,
      environment ∘ payload.firstPort = firstValue ∧
        environment ∘ payload.secondPort = secondValue :=
  exists_commonPort_environment payload.firstPort payload.secondPort
    payload.firstPort_injective payload.secondPort_injective
    payload.commonPorts_covered firstValue secondValue aligned

theorem HeadStripPayload.exists_common_environment
    (payload : HeadStripPayload input first second)
    (firstValue : Fin payload.firstFreePorts → D)
    (secondValue : Fin payload.secondFreePorts → D)
    (aligned : ∀ left right,
      payload.firstPort left = payload.secondPort right →
        firstValue left = secondValue right) :
    ∃ environment : Fin payload.commonPorts → D,
      environment ∘ payload.firstPort = firstValue ∧
        environment ∘ payload.secondPort = secondValue :=
  exists_commonPort_environment payload.firstPort payload.secondPort
    payload.firstPort_injective payload.secondPort_injective
    payload.commonPorts_covered firstValue secondValue aligned

/-- Replacing a term node by a certificate-proved beta-eta equal term preserves its equation. -/
theorem conversion_equiv
    (model : LambdaModel) (environment : Fin ports → model.Carrier)
    (output : model.Carrier) (first second : Term 0 (Fin ports))
    (equivalent : BetaEta first second) :
    output = model.eval first environment ↔
      output = model.eval second environment := by
  rw [model.betaEta_sound equivalent]

/-- Functionality used by congruence joining equal term-node outputs. -/
theorem congruenceJoin_outputs_equal
    (model : LambdaModel) (environment : Fin ports → model.Carrier)
    (firstOutput secondOutput : model.Carrier)
    (first second : Term 0 (Fin ports))
    (equivalent : BetaEta first second)
    (hfirst : firstOutput = model.eval first environment)
    (hsecond : secondOutput = model.eval second environment) :
    firstOutput = secondOutput := by
  rw [hfirst, hsecond]
  exact model.betaEta_sound equivalent

theorem congruenceJoin_equiv
    (model : LambdaModel) (environment : Fin ports → model.Carrier)
    (firstOutput secondOutput : model.Carrier)
    (first second : Term 0 (Fin ports))
    (equivalent : BetaEta first second) :
    (firstOutput = model.eval first environment ∧
        secondOutput = model.eval second environment) ↔
      (firstOutput = model.eval first environment ∧
        secondOutput = model.eval second environment ∧
          firstOutput = secondOutput) := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    exact ⟨hfirst, hsecond,
      congruenceJoin_outputs_equal model environment firstOutput secondOutput
        first second equivalent hfirst hsecond⟩
  · rintro ⟨hfirst, hsecond, _⟩
    exact ⟨hfirst, hsecond⟩

/-- The exact rigid-head theorem consumed by the head-strip gate.  Its premise
is equality of the two node evaluations in the canonical quotient model—the
fact supplied by a shared output wire—not convertibility of the open terms. -/
theorem headStrip_entails
    {ports : Nat} {a b : Term 0 (Fin ports)}
    {sa sb : HeadSpine 0 (Fin ports)}
    (ha : headSpine a = some sa)
    (hb : headSpine b = some sb)
    (sameBinders : sa.binders = sb.binders)
    (headIndex : Fin sa.binders)
    (firstHead : sa.head = .bound headIndex)
    (secondHead : sb.head = .bound (Fin.cast sameBinders headIndex))
    (sameLength : sa.args.length = sb.args.length)
    (environment : Fin ports → Individual)
    (evaluationsEqual : canonicalModel.eval a environment =
      canonicalModel.eval b environment) :
    ∀ index (valid : index < sa.args.length),
      canonicalModel.eval
          (prefixClose sa.binders (sa.args.get ⟨index, valid⟩)) environment =
        canonicalModel.eval
          (prefixClose sb.binders
            (sb.args.get ⟨index, sameLength ▸ valid⟩)) environment := by
  classical
  let representatives : Fin ports → ClosedTerm := fun port =>
    Classical.choose (Quotient.exists_rep (environment port))
  have representatives_quote : ∀ port,
      quote (representatives port) = environment port := by
    intro port
    exact Classical.choose_spec (Quotient.exists_rep (environment port))
  have leftEvaluation := canonicalModel_eval_eq_quote a environment
    representatives representatives_quote
  have rightEvaluation := canonicalModel_eval_eq_quote b environment
    representatives representatives_quote
  have equivalent : BetaEta (a.bindFree representatives)
      (b.bindFree representatives) := by
    apply quote_eq_iff.mp
    exact leftEvaluation.symm.trans
      (evaluationsEqual.trans rightEvaluation)
  have arguments := rigidHead_args_bindFree_bound ha hb sameBinders headIndex
    firstHead secondHead sameLength representatives equivalent
  intro index valid
  let firstArgument :=
    prefixClose sa.binders (sa.args.get ⟨index, valid⟩)
  let secondArgument :=
    prefixClose sb.binders
      (sb.args.get ⟨index, sameLength ▸ valid⟩)
  have argumentEquivalent :
      BetaEta (firstArgument.bindFree representatives)
        (secondArgument.bindFree representatives) :=
    arguments index valid
  have firstQuoted : canonicalModel.eval firstArgument environment =
      quote (firstArgument.bindFree representatives) :=
    canonicalModel_eval_eq_quote firstArgument environment
      representatives representatives_quote
  have quotedEquivalent : quote (firstArgument.bindFree representatives) =
      quote (secondArgument.bindFree representatives) :=
    Quotient.sound argumentEquivalent
  have secondQuoted : canonicalModel.eval secondArgument environment =
      quote (secondArgument.bindFree representatives) :=
    canonicalModel_eval_eq_quote secondArgument environment
      representatives representatives_quote
  exact firstQuoted.trans (quotedEquivalent.trans secondQuoted.symm)

/-- Congruence is the converse half of rigid-head decomposition: equality of
every aligned argument abstraction reconstructs equality of the two complete
rigid-headed terms in the canonical model. -/
theorem headStrip_reflects
    {ports : Nat} {a b : Term 0 (Fin ports)}
    {sa sb : HeadSpine 0 (Fin ports)}
    (ha : headSpine a = some sa)
    (hb : headSpine b = some sb)
    (sameBinders : sa.binders = sb.binders)
    (headIndex : Fin sa.binders)
    (firstHead : sa.head = .bound headIndex)
    (secondHead : sb.head = .bound (Fin.cast sameBinders headIndex))
    (sameLength : sa.args.length = sb.args.length)
    (environment : Fin ports → Individual)
    (argumentsEqual : ∀ index (valid : index < sa.args.length),
      canonicalModel.eval
          (prefixClose sa.binders (sa.args.get ⟨index, valid⟩)) environment =
        canonicalModel.eval
          (prefixClose sb.binders
            (sb.args.get ⟨index, sameLength ▸ valid⟩)) environment) :
    canonicalModel.eval a environment = canonicalModel.eval b environment := by
  classical
  let representatives : Fin ports → ClosedTerm := fun port =>
    Classical.choose (Quotient.exists_rep (environment port))
  have representatives_quote : ∀ port,
      quote (representatives port) = environment port := by
    intro port
    exact Classical.choose_spec (Quotient.exists_rep (environment port))
  have argumentEquivalent : ∀ index (valid : index < sa.args.length),
      BetaEta
        ((prefixClose sa.binders (sa.args.get ⟨index, valid⟩)).bindFree
          representatives)
        ((prefixClose sb.binders
          (sb.args.get ⟨index, sameLength ▸ valid⟩)).bindFree
            representatives) := by
    intro index valid
    apply quote_eq_iff.mp
    have firstQuoted := canonicalModel_eval_eq_quote
      (prefixClose sa.binders (sa.args.get ⟨index, valid⟩)) environment
      representatives representatives_quote
    have secondQuoted := canonicalModel_eval_eq_quote
      (prefixClose sb.binders
        (sb.args.get ⟨index, sameLength ▸ valid⟩)) environment
      representatives representatives_quote
    exact firstQuoted.symm.trans
      ((argumentsEqual index valid).trans secondQuoted)
  have equivalent := rigidHead_of_args_bindFree_bound ha hb sameBinders
    headIndex firstHead secondHead sameLength representatives argumentEquivalent
  have leftEvaluation := canonicalModel_eval_eq_quote a environment
    representatives representatives_quote
  have rightEvaluation := canonicalModel_eval_eq_quote b environment
    representatives representatives_quote
  exact leftEvaluation.trans
    ((Quotient.sound equivalent).trans rightEvaluation.symm)

theorem HeadStripPayload.argumentEvaluationsEqual
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (environment : Fin payload.commonPorts → Individual)
    (evaluationsEqual : canonicalModel.eval
        (payload.firstTerm.mapFree payload.firstPort) environment =
      canonicalModel.eval
        (payload.secondTerm.mapFree payload.secondPort) environment) :
    ∀ index (valid : index < payload.firstSpine.args.length),
      canonicalModel.eval
          (prefixClose payload.firstSpine.binders
            (payload.firstSpine.args.get ⟨index, valid⟩)) environment =
        canonicalModel.eval
          (prefixClose payload.secondSpine.binders
            (payload.secondSpine.args.get
              ⟨index, payload.mappedSameArgumentCount ▸ valid⟩)) environment :=
  headStrip_entails payload.firstSpine_eq payload.secondSpine_eq
    payload.mappedSameBinders payload.headIndex payload.mappedFirstHead
    payload.mappedSecondHead payload.mappedSameArgumentCount environment
    evaluationsEqual

theorem HeadStripPayload.originalArgumentEvaluationsEqual
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (environment : Fin payload.commonPorts → Individual)
    (evaluationsEqual : canonicalModel.eval
        (payload.firstTerm.mapFree payload.firstPort) environment =
      canonicalModel.eval
        (payload.secondTerm.mapFree payload.secondPort) environment)
    (index : Fin payload.firstOriginalSpine.args.length) :
    canonicalModel.eval
        ((payload.firstArgument index).mapFree payload.firstPort) environment =
      canonicalModel.eval
        ((payload.secondArgument index).mapFree payload.secondPort) environment := by
  have valid : index.val < payload.firstSpine.args.length := by
    simpa [HeadStripPayload.firstSpine, HeadSpine.mapFree] using index.isLt
  have h := payload.argumentEvaluationsEqual environment evaluationsEqual
    index.val valid
  simpa [HeadStripPayload.firstSpine, HeadStripPayload.secondSpine,
    HeadSpine.mapFree, HeadStripPayload.firstArgument,
    HeadStripPayload.secondArgument, prefixClose_mapFree] using h

theorem headStrip_replacement_equiv (original arguments : Prop)
    (decompose : original → arguments)
    (reconstruct : arguments → original) :
    original ↔ arguments :=
  ⟨decompose, reconstruct⟩

/-- A closed term always supplies its own fresh existential equality witness. -/
theorem closedTermIntro_valid
    (model : LambdaModel) (term : Term 0 (Fin 0)) :
    ∃ value : model.Carrier, value = model.eval term Fin.elim0 := by
  exact ⟨model.eval term Fin.elim0, rfl⟩

/-- Adding a self-contained valid closed-term equation is an equivalence. -/
theorem closedTermIntro_equiv
    (proposition : Prop) (model : LambdaModel)
    (term : Term 0 (Fin 0)) :
    proposition ↔
      proposition ∧ ∃ value : model.Carrier,
        value = model.eval term Fin.elim0 := by
  constructor
  · intro h
    exact ⟨h, closedTermIntro_valid model term⟩
  · exact And.left

/-- One-point existential substitution, the semantic core of fusion/fission. -/
theorem onePoint_equiv (termValue : D) (body : D → Prop) :
    (∃ value, value = termValue ∧ body value) ↔ body termValue := by
  constructor
  · rintro ⟨value, rfl, hbody⟩
    exact hbody
  · intro hbody
    exact ⟨termValue, rfl, hbody⟩

theorem fusion_equiv (termValue : D) (body : D → Prop) :
    (∃ value, value = termValue ∧ body value) ↔ body termValue :=
  onePoint_equiv termValue body

theorem fission_equiv (termValue : D) (body : D → Prop) :
    body termValue ↔ ∃ value, value = termValue ∧ body value :=
  (onePoint_equiv termValue body).symm

/-- A closed equality witness may be duplicated without changing truth. -/
theorem anchoredWireSplit_equiv (witness rest : Prop) :
    witness ∧ rest ↔ witness ∧ witness ∧ rest := by
  constructor
  · rintro ⟨hwitness, hrest⟩
    exact ⟨hwitness, hwitness, hrest⟩
  · rintro ⟨hwitness, _, hrest⟩
    exact ⟨hwitness, hrest⟩

theorem anchoredWireContract_equiv (witness rest : Prop) :
    witness ∧ witness ∧ rest ↔ witness ∧ rest :=
  (anchoredWireSplit_equiv witness rest).symm

end VisualProof.Rule
