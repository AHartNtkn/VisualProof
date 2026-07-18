import VisualProof.Rule.Soundness
import VisualProof.Rule.Soundness.Congruence
import VisualProof.Rule.Soundness.Equational.AnchoredWireContractInterface
import VisualProof.Rule.Soundness.Equational.AnchoredWireContractCoalescedCompactionOpen
import VisualProof.Rule.Soundness.Equational.HeadStripSimulation
import VisualProof.Diagram.Concrete.Elaboration.Simulation

namespace VisualProof.Rule

open VisualProof
open Diagram
open Theory

private theorem conversion_eraseDups_map_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinjective : Function.Injective f) :
    ∀ values : List α,
      (values.map f).eraseDups = values.eraseDups.map f
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.map_cons]
      congr 1
      rw [← conversion_eraseDups_map_injective f hinjective
        (tail.filter fun value => !value == head)]
      apply congrArg List.eraseDups
      rw [List.filter_map]
      apply congrArg (List.map f)
      apply congrArg (fun predicate => List.filter predicate tail)
      funext value
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp [hinjective.eq_iff]
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem conversion_get_of_eq {left right : List α}
    (equality : left = right) (index : Fin right.length) :
    left.get (Fin.cast (congrArg List.length equality).symm index) =
      right.get index := by
  subst left
  rfl

private theorem conversion_allFin_succ_last (n : Nat) :
    VisualProof.Data.Finite.allFin (n + 1) =
      (VisualProof.Data.Finite.allFin n).map (Fin.castAdd 1) ++
        [Fin.last n] := by
  rw [VisualProof.Data.Finite.allFin_eq_finRange,
    VisualProof.Data.Finite.allFin_eq_finRange, List.finRange_succ_last]
  apply congrArg (fun xs : List (Fin (n + 1)) => xs ++ [Fin.last n])
  apply List.map_congr_left
  intro index _
  apply Fin.ext
  rfl

private theorem conversion_allFin_add (n m : Nat) :
    VisualProof.Data.Finite.allFin (n + m) =
      (VisualProof.Data.Finite.allFin n).map (Fin.castAdd m) ++
        (VisualProof.Data.Finite.allFin m).map (Fin.natAdd n) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, VisualProof.Data.Finite.allFin, List.map_nil,
        List.append_nil]
      have hfun : (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id := by
        funext index
        apply Fin.ext
        rfl
      rw [hfun, List.map_id]
  | succ m ih =>
      change VisualProof.Data.Finite.allFin ((n + m) + 1) = _
      rw [conversion_allFin_succ_last (n + m), ih, List.map_append,
        conversion_allFin_succ_last m, List.map_append, List.map_map,
        List.append_assoc]
      simp only [List.map_map]
      have hleft :
          (Fin.castAdd 1 ∘ Fin.castAdd m : Fin n → Fin ((n + m) + 1)) =
            Fin.castAdd (m + 1) := by
        funext index
        apply Fin.ext
        rfl
      have hmiddle :
          (Fin.castAdd 1 ∘ Fin.natAdd n : Fin m → Fin ((n + m) + 1)) =
            (Fin.natAdd n ∘ Fin.castAdd 1) := by
        funext index
        apply Fin.ext
        rfl
      have hlast : Fin.last (n + m) = Fin.natAdd n (Fin.last m) := by
        apply Fin.ext
        rfl
      rw [hleft, hmiddle, hlast]
      rfl

private def conversionOperationalBoundary
    (boundary : List (Fin input.val.wireCount))
    (payload : ConversionPayload input node) :
    List (Fin (conversionRaw input node payload).wireCount) :=
  boundary.map (Fin.castAdd payload.freshPorts.length)

private def conversionSourceOpen
    (input : Diagram.CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount)) :
    Diagram.OpenConcreteDiagram where
  diagram := input.val
  boundary := boundary

private def conversionTargetOpen
    (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node)
    (boundary : List (Fin input.val.wireCount)) :
    Diagram.OpenConcreteDiagram where
  diagram := conversionRaw input node payload
  boundary := conversionOperationalBoundary boundary payload

private theorem conversionExpectedTransport
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (payload : ConversionPayload input node) :
    (conversionInterfaceTransport input node payload).transportBoundary boundary =
      some (conversionOperationalBoundary boundary payload) := by
  apply InterfaceTransport.transportBoundary_eq_map
  intro wire hwire
  simp [conversionInterfaceTransport, InterfaceTransport.append,
    InterfaceTransport.rootFiltered, conversionRaw, sourceRoot wire hwire]

private def conversionOperationalOpen
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    {receipt : StepReceipt input}
    (realizes : receipt.Realizes (conversionRaw input node payload)
      (conversionWireProvenance input node payload)
      (conversionInterfaceTransport input node payload))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    Diagram.CheckedOpenDiagram signature :=
  ⟨{
    diagram := conversionRaw input node payload
    boundary := conversionOperationalBoundary boundary payload
  }, {
    diagram_well_formed := by
      change (conversionRaw input node payload).WellFormed signature
      have htarget := receipt.result.property
      change receipt.result.val.WellFormed signature at htarget
      rw [realizes.result_eq] at htarget
      exact htarget
    boundary_is_root_scoped :=
      (conversionInterfaceTransport input node payload)
        |>.transportBoundary_root_scoped sourceRoot
          (conversionExpectedTransport boundary sourceRoot payload)
  }⟩

private def conversionOperationalIso
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    {receipt : StepReceipt input}
    (realizes : receipt.Realizes (conversionRaw input node payload)
      (conversionWireProvenance input node payload)
      (conversionInterfaceTransport input node payload))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Diagram.OpenConcreteIso
      (conversionOperationalOpen realizes boundary sourceRoot).val
      (realizes.rawResultOpen mapped) :=
  realizes.operationalIso_to_rawResultOpen htransport
    (conversionOperationalBoundary boundary payload)
    (conversionExpectedTransport boundary sourceRoot payload)

private structure ConversionContextEmbedding
    (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node)
    (source : Diagram.ConcreteElaboration.WireContext input.val)
    (target : Diagram.ConcreteElaboration.WireContext
      (conversionRaw input node payload)) where
  index : Fin source.length → Fin target.length
  get : ∀ i, target.get (index i) =
    Fin.castAdd payload.freshPorts.length (source.get i)
  mem_old : ∀ wire : Fin input.val.wireCount,
    Fin.castAdd payload.freshPorts.length wire ∈ target ↔ wire ∈ source

namespace ConversionContextEmbedding

noncomputable def ofMem
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    {source : Diagram.ConcreteElaboration.WireContext input.val}
    {target : Diagram.ConcreteElaboration.WireContext
      (conversionRaw input node payload)}
    (hmem : ∀ wire : Fin input.val.wireCount,
      Fin.castAdd payload.freshPorts.length wire ∈ target ↔ wire ∈ source) :
    ConversionContextEmbedding input node payload source target where
  index := fun i => Classical.choose
    (Diagram.ConcreteElaboration.WireContext.lookup?_complete
      ((hmem (source.get i)).mpr (List.get_mem source i)))
  get := by
    intro i
    exact Diagram.ConcreteElaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (Diagram.ConcreteElaboration.WireContext.lookup?_complete
          ((hmem (source.get i)).mpr (List.get_mem source i))))
  mem_old := hmem

theorem index_eq_of_get
    (embedding : ConversionContextEmbedding input node payload source target)
    (targetNodup : target.Nodup) (i : Fin source.length)
    (candidate : Fin target.length)
    (hcandidate : target.get candidate =
      Fin.castAdd payload.freshPorts.length (source.get i)) :
    candidate = embedding.index i := by
  obtain ⟨found, hfound⟩ :=
    Diagram.ConcreteElaboration.WireContext.lookup?_complete
      (List.get_mem target candidate)
  have hcandidateFound :=
    Diagram.ConcreteElaboration.WireContext.lookup?_unique targetNodup hfound rfl
  have hembeddingFound :=
    Diagram.ConcreteElaboration.WireContext.lookup?_unique targetNodup hfound
      ((embedding.get i).trans hcandidate.symm)
  exact hcandidateFound.trans hembeddingFound.symm

theorem index_injective
    (embedding : ConversionContextEmbedding input node payload source target)
    (sourceNodup : source.Nodup) : Function.Injective embedding.index := by
  intro first second heq
  have hwires : source.get first = source.get second := by
    have hcast : Fin.castAdd payload.freshPorts.length (source.get first) =
        Fin.castAdd payload.freshPorts.length (source.get second) := by
      rw [← embedding.get first, ← embedding.get second, heq]
    apply Fin.ext
    have hvals := congrArg (fun value => value.val) hcast
    exact hvals
  apply Fin.ext
  exact (List.getElem_inj sourceNodup).mp (by
    simpa only [List.get_eq_getElem] using hwires)

noncomputable def extendEnvironment
    (embedding : ConversionContextEmbedding input node payload source target)
    (sourceNodup : source.Nodup) (fallback : D)
    (sourceEnv : Fin source.length → D) : Fin target.length → D :=
  fun targetIndex =>
    if h : ∃ sourceIndex, embedding.index sourceIndex = targetIndex then
      sourceEnv h.choose
    else fallback

theorem extendEnvironment_index
    (embedding : ConversionContextEmbedding input node payload source target)
    (sourceNodup : source.Nodup) (fallback : D)
    (sourceEnv : Fin source.length → D) :
    embedding.extendEnvironment sourceNodup fallback sourceEnv ∘
        embedding.index = sourceEnv := by
  funext sourceIndex
  simp only [Function.comp_apply, extendEnvironment]
  split
  · rename_i h
    exact congrArg sourceEnv
      (embedding.index_injective sourceNodup h.choose_spec)
  · rename_i h
    exact False.elim (h ⟨sourceIndex, rfl⟩)

end ConversionContextEmbedding

private theorem conversionRaw_otherEndpointOccurs_iff
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (old : Fin input.val.nodeCount) (hne : old ≠ node)
    (wire : Fin input.val.wireCount) (port : Diagram.CPort) :
    (conversionRaw input node payload).EndpointOccurs
        (Fin.castAdd payload.freshPorts.length wire) { node := old, port := port } ↔
      input.val.EndpointOccurs wire { node := old, port := port } := by
  unfold Diagram.ConcreteDiagram.EndpointOccurs
  simp only [conversionRaw, Fin.addCases_left]
  change { node := old, port := port } ∈
      ((input.val.wires wire).endpoints.filter (fun endpoint =>
        if endpoint.node = node then
          match endpoint.port with
          | .free _ => false
          | _ => true
        else true) ++
      (Data.Finite.allFin payload.newFreePorts).filterMap (fun fresh =>
        if payload.existingWire? fresh = some wire then
          some { node := node, port := Diagram.CPort.free fresh }
        else none)) ↔
    { node := old, port := port } ∈ (input.val.wires wire).endpoints
  have hne' : node ≠ old := Ne.symm hne
  simp [hne, hne']

private theorem conversionRaw_otherEndpointOccurs_backward
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (old : Fin input.val.nodeCount) (hne : old ≠ node)
    (targetWire : Fin (conversionRaw input node payload).wireCount)
    (port : Diagram.CPort)
    (hoccurs : (conversionRaw input node payload).EndpointOccurs targetWire
      { node := old, port := port }) :
    ∃ sourceWire : Fin input.val.wireCount,
      Fin.castAdd payload.freshPorts.length sourceWire = targetWire ∧
        input.val.EndpointOccurs sourceWire { node := old, port := port } := by
  change Fin (input.val.wireCount + payload.freshPorts.length) at targetWire
  refine Fin.addCases
    (fun sourceWire h => ⟨sourceWire, rfl,
      (conversionRaw_otherEndpointOccurs_iff old hne sourceWire port).mp h⟩)
    (fun fresh h => ?_) targetWire hoccurs
  unfold Diagram.ConcreteDiagram.EndpointOccurs at h
  simp only [conversionRaw, Fin.addCases_right] at h
  have heq := List.mem_singleton.mp h
  have hold : old = node := congrArg Diagram.CEndpoint.node heq
  exact False.elim (hne hold)

private theorem conversionRaw_outputEndpointOccurs_iff
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (wire : Fin input.val.wireCount) :
    (conversionRaw input node payload).EndpointOccurs
        (Fin.castAdd payload.freshPorts.length wire)
        { node := node, port := .output } ↔
      input.val.EndpointOccurs wire { node := node, port := .output } := by
  unfold Diagram.ConcreteDiagram.EndpointOccurs
  simp only [conversionRaw, Fin.addCases_left]
  change { node := node, port := Diagram.CPort.output } ∈
      ((input.val.wires wire).endpoints.filter (fun endpoint =>
        if endpoint.node = node then
          match endpoint.port with
          | .free _ => false
          | _ => true
        else true) ++
      (Data.Finite.allFin payload.newFreePorts).filterMap (fun fresh =>
        if payload.existingWire? fresh = some wire then
          some { node := node, port := Diagram.CPort.free fresh }
        else none)) ↔
    { node := node, port := Diagram.CPort.output } ∈
      (input.val.wires wire).endpoints
  simp

private theorem conversionRaw_newFree_occurs_of_existing
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (port : Fin payload.newFreePorts) (wire : Fin input.val.wireCount)
    (hexisting : payload.existingWire? port = some wire) :
    (conversionRaw input node payload).EndpointOccurs
      (Fin.castAdd payload.freshPorts.length wire)
      { node := node, port := .free port } := by
  unfold Diagram.ConcreteDiagram.EndpointOccurs
  simp only [conversionRaw, Fin.addCases_left]
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_filterMap.mpr
  refine ⟨port, Data.Finite.mem_allFin port, ?_⟩
  simp [hexisting]

private theorem conversionRaw_resolvedFree_shared
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (source : Diagram.ConcreteElaboration.WireContext input.val)
    (target : Diagram.ConcreteElaboration.WireContext
      (conversionRaw input node payload))
    (embedding : ConversionContextEmbedding input node payload source target)
    (targetNodup : target.Nodup)
    (targetDisjoint :
      (conversionRaw input node payload).WireEndpointsAreDisjoint)
    (sourceFree : Fin payload.oldFreePorts → Fin source.length)
    (targetFree : Fin payload.newFreePorts → Fin target.length)
    (hsource : Diagram.ConcreteElaboration.resolvePorts? input.val source node
      payload.oldFreePorts (fun index => .free index) = some sourceFree)
    (htarget : Diagram.ConcreteElaboration.resolvePorts?
      (conversionRaw input node payload) target node payload.newFreePorts
      (fun index => .free index) = some targetFree)
    (old : Fin payload.oldFreePorts) (new : Fin payload.newFreePorts)
    (hshared : payload.oldPort old = payload.newPort new) :
    targetFree new = embedding.index (sourceFree old) := by
  have hsourcePort := VisualProof.Data.Finite.sequenceFin_sound hsource old
  have htargetPort := VisualProof.Data.Finite.sequenceFin_sound htarget new
  obtain ⟨sourceWire, hsourceOccurs, hsourceGet⟩ :=
    Diagram.ConcreteElaboration.resolvePort?_sound hsourcePort
  obtain ⟨targetWire, htargetOccurs, htargetGet⟩ :=
    Diagram.ConcreteElaboration.resolvePort?_sound htargetPort
  obtain ⟨sharedWire, hexisting, hsharedOccurs⟩ :=
    payload.existingWire?_of_shared hshared
  have hsourceWire : sourceWire = sharedWire :=
    Diagram.ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint
      hsourceOccurs hsharedOccurs
  have htargetSharedOccurs :
      (conversionRaw input node payload).EndpointOccurs
        (Fin.castAdd payload.freshPorts.length sharedWire)
        { node := node, port := .free new } :=
    conversionRaw_newFree_occurs_of_existing new sharedWire hexisting
  have htargetWire : targetWire =
      Fin.castAdd payload.freshPorts.length sharedWire :=
    Diagram.ConcreteElaboration.endpoint_wire_unique targetDisjoint htargetOccurs
      htargetSharedOccurs
  apply embedding.index_eq_of_get targetNodup
  calc
    target.get (targetFree new) = targetWire := by
      simpa only [List.get_eq_getElem] using htargetGet
    _ = Fin.castAdd payload.freshPorts.length sharedWire := htargetWire
    _ = Fin.castAdd payload.freshPorts.length sourceWire :=
      congrArg (Fin.castAdd payload.freshPorts.length) hsourceWire.symm
    _ = Fin.castAdd payload.freshPorts.length
        (source.get (sourceFree old)) := by
      congr 1
      simpa only [List.get_eq_getElem] using hsourceGet.symm

private theorem conversionRaw_resolvedOutput
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (source : Diagram.ConcreteElaboration.WireContext input.val)
    (target : Diagram.ConcreteElaboration.WireContext
      (conversionRaw input node payload))
    (embedding : ConversionContextEmbedding input node payload source target)
    (targetNodup : target.Nodup)
    (targetDisjoint :
      (conversionRaw input node payload).WireEndpointsAreDisjoint)
    (sourceOutput : Fin source.length) (targetOutput : Fin target.length)
    (hsource : Diagram.ConcreteElaboration.resolvePort? input.val source node
      .output = some sourceOutput)
    (htarget : Diagram.ConcreteElaboration.resolvePort?
      (conversionRaw input node payload) target node .output =
        some targetOutput) :
    targetOutput = embedding.index sourceOutput := by
  obtain ⟨sourceWire, hsourceOccurs, hsourceGet⟩ :=
    Diagram.ConcreteElaboration.resolvePort?_sound hsource
  obtain ⟨targetWire, htargetOccurs, htargetGet⟩ :=
    Diagram.ConcreteElaboration.resolvePort?_sound htarget
  have hmappedOccurs :
      (conversionRaw input node payload).EndpointOccurs
        (Fin.castAdd payload.freshPorts.length sourceWire)
        { node := node, port := .output } :=
    (conversionRaw_outputEndpointOccurs_iff sourceWire).mpr hsourceOccurs
  have htargetWire : targetWire =
      Fin.castAdd payload.freshPorts.length sourceWire :=
    Diagram.ConcreteElaboration.endpoint_wire_unique targetDisjoint
      htargetOccurs hmappedOccurs
  apply embedding.index_eq_of_get targetNodup
  calc
    target.get targetOutput = targetWire := by
      simpa only [List.get_eq_getElem] using htargetGet
    _ = Fin.castAdd payload.freshPorts.length sourceWire := htargetWire
    _ = Fin.castAdd payload.freshPorts.length (source.get sourceOutput) := by
      congr 1
      simpa only [List.get_eq_getElem] using hsourceGet.symm

private theorem conversionRaw_compileNode?_other
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    {rels : Theory.RelCtx}
    (source : Diagram.ConcreteElaboration.WireContext input.val)
    (target : Diagram.ConcreteElaboration.WireContext
      (conversionRaw input node payload))
    (embedding : ConversionContextEmbedding input node payload source target)
    (binders : Diagram.ConcreteElaboration.BinderContext input.val rels)
    (targetNodup : target.Nodup)
    (targetDisjoint :
      (conversionRaw input node payload).WireEndpointsAreDisjoint)
    (old : Fin input.val.nodeCount) (hne : old ≠ node) :
    Diagram.ConcreteElaboration.compileNode? signature
        (conversionRaw input node payload) target binders old =
      (Diagram.ConcreteElaboration.compileNode? signature input.val source
        binders old).map (Diagram.Item.renameWires embedding.index) := by
  let converted := conversionRaw input node payload
  let targetOld : Fin converted.nodeCount := old
  have hports : ∀ endpointPort,
      Diagram.ConcreteElaboration.resolvePort? converted target targetOld endpointPort =
        (Diagram.ConcreteElaboration.resolvePort? input.val source old
          endpointPort).map embedding.index := by
    intro endpointPort
    apply Diagram.ConcreteElaboration.resolvePort?_map_of_occurrence
      source target old targetOld (Fin.castAdd payload.freshPorts.length)
      embedding.index targetNodup embedding.get embedding.mem_old
    · intro wire candidatePort hoccurs
      simpa [targetOld] using
        (conversionRaw_otherEndpointOccurs_iff old hne wire
          candidatePort).mpr hoccurs
    · intro targetWire candidatePort hoccurs
      exact conversionRaw_otherEndpointOccurs_backward old hne targetWire
        candidatePort (by simpa [targetOld] using hoccurs)
    · exact targetDisjoint
  have hbinders : ∀ region binder,
      input.val.nodes old = .atom region binder →
        binders binder =
          (binders binder).map (fun relation =>
            ⟨relation.1, (fun {_} relation => relation) relation.2⟩) := by
    intro region binder _
    simp
  dsimp only [converted] at hports
  dsimp only [targetOld] at hports
  have htargetNode : (conversionRaw input node payload).nodes old =
      input.val.nodes old := by
    simp [conversionRaw, hne]
  unfold Diagram.ConcreteElaboration.compileNode?
  rw [htargetNode]
  cases hsourceNode : input.val.nodes old with
  | term region freePorts term =>
      simp only [hsourceNode]
      rw [hports .output]
      have hfree := Diagram.ConcreteElaboration.resolvePorts?_map source target
        old old embedding.index freePorts (fun index => .free index) hports
      rw [hfree]
      cases houtput : Diagram.ConcreteElaboration.resolvePort? input.val source
          old .output <;> simp [houtput]
      cases hfreeSource : Diagram.ConcreteElaboration.resolvePorts? input.val
          source old freePorts (fun index => .free index) <;>
        simp [hfreeSource, Diagram.Item.renameWires,
          Lambda.Term.mapFree_comp, Function.comp_def]
  | atom region binder =>
      simp only [hsourceNode]
      cases hrelation : binders binder with
      | none => simp [hrelation]
      | some relation =>
          cases relation with
          | mk arity relation =>
              dsimp
              have harguments := Diagram.ConcreteElaboration.resolvePorts?_map
                source target old old embedding.index arity
                (fun index => .arg index) hports
              rw [harguments]
              cases hsourceArguments : Diagram.ConcreteElaboration.resolvePorts?
                  input.val source old arity (fun index => .arg index) <;>
                simp [hrelation, hsourceArguments, Diagram.Item.renameWires,
                  Function.comp_def]
  | named region definition arity =>
      simp only [hsourceNode]
      have harguments := Diagram.ConcreteElaboration.resolvePorts?_map source
        target old old embedding.index arity (fun index => .arg index) hports
      rw [harguments]
      cases hrelation : Diagram.ConcreteElaboration.namedRel? signature
          definition arity <;> simp [hrelation]
      cases hsourceArguments : Diagram.ConcreteElaboration.resolvePorts?
          input.val source old arity (fun index => .arg index) <;>
        simp [hsourceArguments, Diagram.Item.renameWires, Function.comp_def]

private theorem conversionRaw_compileNode_denote_iff
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    {rels : Theory.RelCtx}
    (source : Diagram.ConcreteElaboration.WireContext input.val)
    (target : Diagram.ConcreteElaboration.WireContext
      (conversionRaw input node payload))
    (embedding : ConversionContextEmbedding input node payload source target)
    (binders : Diagram.ConcreteElaboration.BinderContext input.val rels)
    (targetNodup : target.Nodup)
    (targetDisjoint :
      (conversionRaw input node payload).WireEndpointsAreDisjoint)
    (sourceItem : Diagram.Item signature source.length rels)
    (targetItem : Diagram.Item signature target.length rels)
    (hsourceCompile : Diagram.ConcreteElaboration.compileNode? signature
      input.val source binders node = some sourceItem)
    (htargetCompile : Diagram.ConcreteElaboration.compileNode? signature
      (conversionRaw input node payload) target binders node = some targetItem)
    (model : Lambda.LambdaModel)
    (named : Diagram.NamedEnv model.Carrier signature)
    (targetEnv : Fin target.length → model.Carrier)
    (relEnv : Diagram.RelEnv model.Carrier rels) :
    Diagram.denoteItem model named (targetEnv ∘ embedding.index) relEnv
        sourceItem ↔
      Diagram.denoteItem model named targetEnv relEnv targetItem := by
  have htargetNode : (conversionRaw input node payload).nodes node =
      .term payload.region payload.newFreePorts payload.newTerm := by
    simp [conversionRaw]
  unfold Diagram.ConcreteElaboration.compileNode? at hsourceCompile htargetCompile
  rw [payload.node_eq] at hsourceCompile
  rw [htargetNode] at htargetCompile
  cases hsourceOutput : Diagram.ConcreteElaboration.resolvePort? input.val
      source node .output with
  | none => simp [hsourceOutput] at hsourceCompile
  | some sourceOutput =>
      cases hsourceFree : Diagram.ConcreteElaboration.resolvePorts? input.val
          source node payload.oldFreePorts (fun index => .free index) with
      | none => simp [hsourceOutput, hsourceFree] at hsourceCompile
      | some sourceFree =>
          cases htargetOutput : Diagram.ConcreteElaboration.resolvePort?
              (conversionRaw input node payload) target node .output with
          | none => simp [htargetOutput] at htargetCompile
          | some targetOutput =>
              cases htargetFree : Diagram.ConcreteElaboration.resolvePorts?
                  (conversionRaw input node payload) target node
                  payload.newFreePorts (fun index => .free index) with
              | none =>
                  simp [htargetOutput, htargetFree] at htargetCompile
              | some targetFree =>
                  simp [hsourceOutput, hsourceFree] at hsourceCompile
                  simp [htargetOutput, htargetFree] at htargetCompile
                  subst sourceItem
                  subst targetItem
                  have houtput := conversionRaw_resolvedOutput source target
                    embedding targetNodup targetDisjoint sourceOutput targetOutput
                    hsourceOutput htargetOutput
                  let oldValue : Fin payload.oldFreePorts → model.Carrier :=
                    (targetEnv ∘ embedding.index) ∘ sourceFree
                  let newValue : Fin payload.newFreePorts → model.Carrier :=
                    targetEnv ∘ targetFree
                  have haligned : ∀ old new,
                      payload.oldPort old = payload.newPort new →
                        oldValue old = newValue new := by
                    intro old new hshared
                    have hindex := conversionRaw_resolvedFree_shared source target
                      embedding targetNodup targetDisjoint sourceFree targetFree
                      hsourceFree htargetFree old new hshared
                    simp only [oldValue, newValue, Function.comp_apply]
                    rw [hindex]
                  obtain ⟨commonEnv, hold, hnew⟩ :=
                    payload.exists_common_environment oldValue newValue haligned
                  have heval : model.eval payload.oldTerm oldValue =
                      model.eval payload.newTerm newValue := by
                    calc
                      model.eval payload.oldTerm oldValue =
                          model.eval payload.oldTerm
                            (commonEnv ∘ payload.oldPort) := by rw [hold]
                      _ = model.eval payload.newTerm
                            (commonEnv ∘ payload.newPort) :=
                        payload.eval_eq model commonEnv
                      _ = model.eval payload.newTerm newValue := by rw [hnew]
                  simp only [Diagram.denoteItem_equation,
                    Lambda.LambdaModel.eval_mapFree]
                  change targetEnv (embedding.index sourceOutput) =
                      model.eval payload.oldTerm oldValue ↔
                    targetEnv targetOutput =
                      model.eval payload.newTerm newValue
                  rw [houtput, heval]

private theorem conversionRaw_oldWire_scope
    (wire : Fin input.val.wireCount) :
    ((conversionRaw input node payload).wires
      (Fin.castAdd payload.freshPorts.length wire)).scope =
        (input.val.wires wire).scope := by
  simp [conversionRaw]

private theorem conversionRaw_exactScopeWires_mem_old_iff
    (region : Fin input.val.regionCount)
    (wire : Fin input.val.wireCount) :
    Fin.castAdd payload.freshPorts.length wire ∈
        Diagram.ConcreteElaboration.exactScopeWires
          (conversionRaw input node payload) region ↔
      wire ∈ Diagram.ConcreteElaboration.exactScopeWires input.val region := by
  constructor
  · intro hmem
    have hscope := (Diagram.ConcreteElaboration.mem_exactScopeWires
      (conversionRaw input node payload) region
      (Fin.castAdd payload.freshPorts.length wire)).mp hmem
    rw [conversionRaw_oldWire_scope] at hscope
    exact (Diagram.ConcreteElaboration.mem_exactScopeWires
      input.val region wire).mpr hscope
  · intro hmem
    have hscope := (Diagram.ConcreteElaboration.mem_exactScopeWires
      input.val region wire).mp hmem
    apply (Diagram.ConcreteElaboration.mem_exactScopeWires
      (conversionRaw input node payload) region
      (Fin.castAdd payload.freshPorts.length wire)).mpr
    rw [conversionRaw_oldWire_scope]
    exact hscope

namespace ConversionContextEmbedding

noncomputable def extend
    (embedding : ConversionContextEmbedding input node payload source target)
    (region : Fin input.val.regionCount) :
    ConversionContextEmbedding input node payload
      (source.extend region) (target.extend region) :=
  ofMem (by
    intro wire
    unfold Diagram.ConcreteElaboration.WireContext.extend
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hinherited | hlocal
      · exact List.mem_append_left _ ((embedding.mem_old wire).mp hinherited)
      · exact List.mem_append_right _
          ((conversionRaw_exactScopeWires_mem_old_iff region wire).mp hlocal)
    · intro hmem
      rcases List.mem_append.mp hmem with hinherited | hlocal
      · exact List.mem_append_left _ ((embedding.mem_old wire).mpr hinherited)
      · exact List.mem_append_right _
          ((conversionRaw_exactScopeWires_mem_old_iff region wire).mpr hlocal))

end ConversionContextEmbedding

private theorem conversionRaw_exactScopeWires
    (region : Fin input.val.regionCount) :
    Diagram.ConcreteElaboration.exactScopeWires
        (conversionRaw input node payload) region =
      (Diagram.ConcreteElaboration.exactScopeWires input.val region).map
          (Fin.castAdd payload.freshPorts.length) ++
        if region = payload.region then
          (VisualProof.Data.Finite.allFin payload.freshPorts.length).map
            (Fin.natAdd input.val.wireCount)
        else [] := by
  unfold Diagram.ConcreteElaboration.exactScopeWires
    VisualProof.Data.Finite.filterFin
  change List.filter _
      (VisualProof.Data.Finite.allFin
        (input.val.wireCount + payload.freshPorts.length)) = _
  rw [conversion_allFin_add, List.filter_append]
  simp only [List.filter_map]
  congr 1
  · apply congrArg (List.map (Fin.castAdd payload.freshPorts.length))
    apply congrArg (fun predicate => List.filter predicate
      (VisualProof.Data.Finite.allFin input.val.wireCount))
    funext wire
    simp only [Function.comp_apply]
    rw [conversionRaw_oldWire_scope]
    rfl
  · split <;> rename_i hregion
    · subst region
      apply congrArg (List.map (Fin.natAdd input.val.wireCount))
      apply List.filter_eq_self.mpr
      intro fresh _
      simp only [Function.comp_apply, conversionRaw, Fin.addCases_right,
        decide_eq_true_eq]
    · change List.map (Fin.natAdd input.val.wireCount)
          (List.filter _
            (VisualProof.Data.Finite.allFin payload.freshPorts.length)) =
          List.map (Fin.natAdd input.val.wireCount) []
      apply congrArg (List.map (Fin.natAdd input.val.wireCount))
      apply List.filter_eq_nil_iff.mpr
      intro fresh _ heq
      have hdecide : decide
          (((conversionRaw input node payload).wires
            (Fin.natAdd input.val.wireCount fresh)).scope = region) = true :=
        heq
      have hscope := decide_eq_true_eq.mp hdecide
      simp only [conversionRaw, Fin.addCases_right] at hscope
      exact hregion hscope.symm

private theorem conversionRaw_exactScopeWires_length_of_ne
    (region : Fin input.val.regionCount) (hne : region ≠ payload.region) :
    (Diagram.ConcreteElaboration.exactScopeWires
      (conversionRaw input node payload) region).length =
      (Diagram.ConcreteElaboration.exactScopeWires input.val region).length := by
  rw [conversionRaw_exactScopeWires, if_neg hne, List.append_nil]
  exact List.length_map _

private theorem conversionTargetOpen_exposedWires
    (boundary : List (Fin input.val.wireCount)) :
    (conversionTargetOpen input node payload boundary).exposedWires =
      (conversionSourceOpen input boundary).exposedWires.map
        (Fin.castAdd payload.freshPorts.length) := by
  unfold conversionTargetOpen conversionSourceOpen conversionOperationalBoundary
    Diagram.OpenConcreteDiagram.exposedWires
  have injective : Function.Injective
      (Fin.castAdd payload.freshPorts.length : Fin input.val.wireCount →
        Fin (input.val.wireCount + payload.freshPorts.length)) := by
    intro left right equality
    apply Fin.ext
    exact congrArg
      (fun value : Fin (input.val.wireCount + payload.freshPorts.length) =>
        value.val) equality
  exact conversion_eraseDups_map_injective _ injective _

private theorem conversionTargetOpen_hiddenWires
    (boundary : List (Fin input.val.wireCount)) :
    (conversionTargetOpen input node payload boundary).hiddenWires =
      (conversionSourceOpen input boundary).hiddenWires.map
          (Fin.castAdd payload.freshPorts.length : Fin input.val.wireCount →
            Fin (input.val.wireCount + payload.freshPorts.length)) ++
        if input.val.root = payload.region then
          (VisualProof.Data.Finite.allFin payload.freshPorts.length).map
            (Fin.natAdd input.val.wireCount)
        else [] := by
  unfold Diagram.OpenConcreteDiagram.hiddenWires
  change List.filter
      (fun wire => decide
        (wire ∉ (conversionTargetOpen input node payload boundary).exposedWires))
      (Diagram.ConcreteElaboration.exactScopeWires
        (conversionRaw input node payload) input.val.root) = _
  rw [conversionRaw_exactScopeWires, conversionTargetOpen_exposedWires]
  have oldPart :
      List.filter
          (fun wire => decide
            (wire ∉ (conversionSourceOpen input boundary).exposedWires.map
              (Fin.castAdd payload.freshPorts.length)))
          (List.map (Fin.castAdd payload.freshPorts.length)
            (Diagram.ConcreteElaboration.exactScopeWires input.val
              input.val.root)) =
        List.map (Fin.castAdd payload.freshPorts.length)
          (List.filter
            (fun wire => decide
              (wire ∉ (conversionSourceOpen input boundary).exposedWires))
            (Diagram.ConcreteElaboration.exactScopeWires input.val
              input.val.root)) := by
    rw [List.filter_map]
    apply congrArg (List.map (Fin.castAdd payload.freshPorts.length))
    apply congrArg (fun predicate => List.filter predicate
      (Diagram.ConcreteElaboration.exactScopeWires input.val input.val.root))
    funext wire
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro notMapped sourceMember
      exact notMapped (List.mem_map.mpr ⟨wire, sourceMember, rfl⟩)
    · intro notSource mappedMember
      rcases List.mem_map.mp mappedMember with ⟨old, oldMember, equality⟩
      change Fin.castAdd payload.freshPorts.length old =
        Fin.castAdd payload.freshPorts.length wire at equality
      have oldEq : old = wire := by
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.val.wireCount + payload.freshPorts.length) =>
            value.val) equality
      exact notSource (by simpa [oldEq] using oldMember)
  by_cases rootSite : input.val.root = payload.region
  · rw [if_pos rootSite]
    have split := List.filter_append
      (p := fun wire => decide
        (wire ∉ (conversionSourceOpen input boundary).exposedWires.map
          (Fin.castAdd payload.freshPorts.length)))
      (List.map (Fin.castAdd payload.freshPorts.length)
        (Diagram.ConcreteElaboration.exactScopeWires input.val input.val.root))
      ((VisualProof.Data.Finite.allFin payload.freshPorts.length).map
        (Fin.natAdd input.val.wireCount))
    apply Eq.trans split
    rw [oldPart]
    congr 1
    apply List.filter_eq_self.mpr
    intro fresh freshMember
    rcases List.mem_map.mp freshMember with ⟨index, _, rfl⟩
    apply decide_eq_true
    intro exposed
    unfold conversionSourceOpen at exposed
    rcases List.mem_map.mp exposed with ⟨old, _, equality⟩
    change Fin.castAdd payload.freshPorts.length old =
      Fin.natAdd input.val.wireCount index at equality
    have values := congrArg
      (fun value : Fin (input.val.wireCount + payload.freshPorts.length) =>
        value.val) equality
    simp only [Fin.val_castAdd, Fin.val_natAdd] at values
    omega
  · rw [if_neg rootSite, List.append_nil]
    simpa [conversionSourceOpen] using oldPart

private theorem conversionTargetOpen_rootWires
    (boundary : List (Fin input.val.wireCount)) :
    (conversionTargetOpen input node payload boundary).rootWires =
      (conversionSourceOpen input boundary).rootWires.map
          (Fin.castAdd payload.freshPorts.length : Fin input.val.wireCount →
            Fin (input.val.wireCount + payload.freshPorts.length)) ++
        if input.val.root = payload.region then
          (VisualProof.Data.Finite.allFin payload.freshPorts.length).map
            (Fin.natAdd input.val.wireCount)
        else [] := by
  unfold Diagram.OpenConcreteDiagram.rootWires
  rw [conversionTargetOpen_exposedWires,
    conversionTargetOpen_hiddenWires]
  have mappedAppend :
      List.map (Fin.castAdd payload.freshPorts.length :
          Fin input.val.wireCount →
            Fin (input.val.wireCount + payload.freshPorts.length))
          ((conversionSourceOpen input boundary).exposedWires ++
            (conversionSourceOpen input boundary).hiddenWires) =
        List.map (Fin.castAdd payload.freshPorts.length)
            (conversionSourceOpen input boundary).exposedWires ++
          List.map (Fin.castAdd payload.freshPorts.length)
            (conversionSourceOpen input boundary).hiddenWires := by
    exact List.map_append
  by_cases rootSite : input.val.root = payload.region
  · simp only [if_pos rootSite]
    rw [mappedAppend]
    exact (List.append_assoc _ _ _).symm
  · simp only [if_neg rootSite, List.append_nil]
    rw [mappedAppend]
    rfl

private def conversionRootFresh
    (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node) :
    List (Fin (input.val.wireCount + payload.freshPorts.length)) :=
  if input.val.root = payload.region then
    (VisualProof.Data.Finite.allFin payload.freshPorts.length).map
      (Fin.natAdd input.val.wireCount)
  else []

private noncomputable def conversionRootIndex
    (boundary : List (Fin input.val.wireCount)) :
    Fin (conversionSourceOpen input boundary).rootWires.length →
      Fin (conversionTargetOpen input node payload boundary).rootWires.length :=
  fun index =>
    let mapped := List.map (Fin.castAdd payload.freshPorts.length :
        Fin input.val.wireCount →
          Fin (input.val.wireCount + payload.freshPorts.length))
      (conversionSourceOpen input boundary).rootWires ++
        conversionRootFresh input node payload
    let mappedIndex : Fin mapped.length := ⟨index.val, by
      show index.val <
        (List.map (Fin.castAdd payload.freshPorts.length :
            Fin input.val.wireCount →
              Fin (input.val.wireCount + payload.freshPorts.length))
            (conversionSourceOpen input boundary).rootWires ++
          conversionRootFresh input node payload).length
      rw [List.length_append, List.length_map]
      exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩
    Fin.cast
      (congrArg List.length
        (conversionTargetOpen_rootWires
          (input := input) (node := node) (payload := payload) boundary)).symm
      mappedIndex

private theorem conversionRootIndex_get
    (boundary : List (Fin input.val.wireCount))
    (index : Fin (conversionSourceOpen input boundary).rootWires.length) :
    (conversionTargetOpen input node payload boundary).rootWires.get
        (conversionRootIndex boundary index) =
      Fin.castAdd payload.freshPorts.length
        ((conversionSourceOpen input boundary).rootWires.get index) := by
  let mapped := List.map (Fin.castAdd payload.freshPorts.length :
      Fin input.val.wireCount →
        Fin (input.val.wireCount + payload.freshPorts.length))
    (conversionSourceOpen input boundary).rootWires ++
      conversionRootFresh input node payload
  let mappedIndex : Fin mapped.length := ⟨index.val, by
    show index.val <
      (List.map (Fin.castAdd payload.freshPorts.length :
          Fin input.val.wireCount →
            Fin (input.val.wireCount + payload.freshPorts.length))
          (conversionSourceOpen input boundary).rootWires ++
        conversionRootFresh input node payload).length
    rw [List.length_append, List.length_map]
    exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩
  have transported := conversion_get_of_eq
    (conversionTargetOpen_rootWires
      (input := input) (node := node) (payload := payload) boundary)
    mappedIndex
  change (conversionTargetOpen input node payload boundary).rootWires.get
      (conversionRootIndex boundary index) = _
  rw [show conversionRootIndex boundary index =
      Fin.cast
        (congrArg List.length
          (conversionTargetOpen_rootWires
            (input := input) (node := node) (payload := payload) boundary)).symm
        mappedIndex by rfl]
  rw [transported]
  change mapped.get mappedIndex = _
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by
    change index.val <
      (List.map (Fin.castAdd payload.freshPorts.length)
        (conversionSourceOpen input boundary).rootWires).length
    rw [List.length_map]
    exact index.isLt)]
  exact List.getElem_map _

private def conversionSourceCheckedOpen
    (input : Diagram.CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    Diagram.CheckedOpenDiagram signature :=
  ⟨conversionSourceOpen input boundary, {
    diagram_well_formed := input.property
    boundary_is_root_scoped := sourceRoot
  }⟩

private def conversionTargetCheckedOpen
    (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (htarget : (conversionRaw input node payload).WellFormed signature) :
    Diagram.CheckedOpenDiagram signature :=
  ⟨conversionTargetOpen input node payload boundary, {
    diagram_well_formed := htarget
    boundary_is_root_scoped := by
      intro targetWire member
      change targetWire ∈ boundary.map
        (Fin.castAdd payload.freshPorts.length) at member
      rcases List.mem_map.mp member with ⟨sourceWire, sourceMember, equality⟩
      subst targetWire
      unfold conversionTargetOpen
      rw [conversionRaw_oldWire_scope]
      exact sourceRoot sourceWire sourceMember
  }⟩

private noncomputable def conversionRootEmbedding
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire : Fin input.val.wireCount, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (htarget : (conversionRaw input node payload).WellFormed signature) :
    ConversionContextEmbedding input node payload
      (conversionSourceOpen input boundary).rootWires
      (conversionTargetOpen input node payload boundary).rootWires :=
  ConversionContextEmbedding.ofMem (by
    intro wire
    constructor
    · intro member
      have scope := (Diagram.OpenConcreteDiagram.mem_rootWires_iff
        (conversionTargetCheckedOpen input node payload boundary sourceRoot
          htarget).val
        (conversionTargetCheckedOpen input node payload boundary sourceRoot
          htarget).property _).mp member
      change ((conversionRaw input node payload).wires
          (Fin.castAdd payload.freshPorts.length wire)).scope = input.val.root
        at scope
      rw [conversionRaw_oldWire_scope] at scope
      exact (Diagram.OpenConcreteDiagram.mem_rootWires_iff
        (conversionSourceCheckedOpen input boundary sourceRoot).val
        (conversionSourceCheckedOpen input boundary sourceRoot).property _).mpr
          scope
    · intro member
      have scope := (Diagram.OpenConcreteDiagram.mem_rootWires_iff
        (conversionSourceCheckedOpen input boundary sourceRoot).val
        (conversionSourceCheckedOpen input boundary sourceRoot).property _).mp
          member
      apply (Diagram.OpenConcreteDiagram.mem_rootWires_iff
        (conversionTargetCheckedOpen input node payload boundary sourceRoot
          htarget).val
        (conversionTargetCheckedOpen input node payload boundary sourceRoot
          htarget).property _).mpr
      change ((conversionRaw input node payload).wires
          (Fin.castAdd payload.freshPorts.length wire)).scope = input.val.root
      rw [conversionRaw_oldWire_scope]
      exact scope)

private theorem conversionRootEmbedding_index
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire : Fin input.val.wireCount, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (htarget : (conversionRaw input node payload).WellFormed signature)
    (index : Fin (conversionSourceOpen input boundary).rootWires.length) :
    (conversionRootEmbedding boundary sourceRoot htarget).index index =
      conversionRootIndex boundary index := by
  symm
  apply ConversionContextEmbedding.index_eq_of_get
    (conversionRootEmbedding boundary sourceRoot htarget)
    (conversionTargetOpen input node payload boundary).rootWires_nodup index
  exact conversionRootIndex_get boundary index

private theorem conversionTargetOpen_exposed_length
    (boundary : List (Fin input.val.wireCount)) :
    (conversionTargetOpen input node payload boundary).exposedWires.length =
      (conversionSourceOpen input boundary).exposedWires.length := by
  rw [conversionTargetOpen_exposedWires]
  change (List.map (Fin.castAdd payload.freshPorts.length :
      Fin input.val.wireCount →
        Fin (input.val.wireCount + payload.freshPorts.length))
      (conversionSourceOpen input boundary).exposedWires).length = _
  exact List.length_map _

private theorem conversionTargetOpen_hidden_length
    (boundary : List (Fin input.val.wireCount)) :
    (conversionTargetOpen input node payload boundary).hiddenWires.length =
      (conversionSourceOpen input boundary).hiddenWires.length +
        (conversionRootFresh input node payload).length := by
  rw [conversionTargetOpen_hiddenWires]
  change (List.map (Fin.castAdd payload.freshPorts.length :
      Fin input.val.wireCount →
        Fin (input.val.wireCount + payload.freshPorts.length))
      (conversionSourceOpen input boundary).hiddenWires ++
        conversionRootFresh input node payload).length = _
  rw [List.length_append, List.length_map]
  rfl

private def conversionExposedIndex
    (boundary : List (Fin input.val.wireCount)) :
    Fin (conversionSourceOpen input boundary).exposedWires.length →
      Fin (conversionTargetOpen input node payload boundary).exposedWires.length :=
  Fin.cast (conversionTargetOpen_exposed_length
    (input := input) (node := node) (payload := payload) boundary).symm

private theorem conversionBoundaryLengthEq
    (boundary : List (Fin input.val.wireCount)) :
    (conversionTargetOpen input node payload boundary).boundary.length =
      (conversionSourceOpen input boundary).boundary.length := by
  simp [conversionTargetOpen, conversionSourceOpen, conversionOperationalBoundary]

private def conversionSourceExposedIndex
    (boundary : List (Fin input.val.wireCount)) :
    Fin (conversionTargetOpen input node payload boundary).exposedWires.length →
      Fin (conversionSourceOpen input boundary).exposedWires.length :=
  Fin.cast (conversionTargetOpen_exposed_length
    (input := input) (node := node) (payload := payload) boundary)

private theorem conversionExposedIndex_sourceExposedIndex
    (boundary : List (Fin input.val.wireCount))
    (index : Fin
      (conversionTargetOpen input node payload boundary).exposedWires.length) :
    conversionExposedIndex (input := input) (node := node) (payload := payload)
        boundary
        (conversionSourceExposedIndex (input := input) (node := node)
          (payload := payload) boundary index) = index := by
  apply Fin.ext
  rfl

private theorem conversionSourceExposedIndex_exposedIndex
    (boundary : List (Fin input.val.wireCount))
    (index : Fin (conversionSourceOpen input boundary).exposedWires.length) :
    conversionSourceExposedIndex (input := input) (node := node)
        (payload := payload) boundary
        (conversionExposedIndex (input := input) (node := node)
          (payload := payload) boundary index) = index := by
  apply Fin.ext
  rfl

private theorem conversionExposedIndex_get
    (boundary : List (Fin input.val.wireCount))
    (index : Fin (conversionSourceOpen input boundary).exposedWires.length) :
    (conversionTargetOpen input node payload boundary).exposedWires.get
        (conversionExposedIndex boundary index) =
      Fin.castAdd payload.freshPorts.length
        ((conversionSourceOpen input boundary).exposedWires.get index) := by
  let mapped := (conversionSourceOpen input boundary).exposedWires.map
    (Fin.castAdd payload.freshPorts.length)
  let mappedIndex : Fin mapped.length :=
    Fin.cast (List.length_map
      (f := Fin.castAdd payload.freshPorts.length)
      (as := (conversionSourceOpen input boundary).exposedWires)).symm index
  have transported := conversion_get_of_eq
    (conversionTargetOpen_exposedWires
      (input := input) (node := node) (payload := payload) boundary)
    mappedIndex
  rw [show conversionExposedIndex boundary index =
      Fin.cast (congrArg List.length
        (conversionTargetOpen_exposedWires
          (input := input) (node := node) (payload := payload) boundary)).symm
        mappedIndex by apply Fin.ext; rfl]
  rw [transported]
  change mapped.get mappedIndex = _
  simp [mapped, mappedIndex, List.get_eq_getElem]

private theorem conversionBoundaryClass
    (boundary : List (Fin input.val.wireCount))
    (position : Fin (conversionSourceOpen input boundary).boundary.length) :
    conversionExposedIndex boundary
        ((conversionSourceOpen input boundary).boundaryClass position) =
      (conversionTargetOpen input node payload boundary).boundaryClass
        (Fin.cast (conversionBoundaryLengthEq boundary).symm position) := by
  apply Diagram.OpenConcreteDiagram.boundaryClass_complete
  rw [conversionExposedIndex_get,
    Diagram.OpenConcreteDiagram.boundaryClass_sound]
  simp [conversionTargetOpen, conversionSourceOpen, conversionOperationalBoundary,
    List.get_eq_getElem]

private theorem conversionRootEnvironment_forward
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    {D : Type}
    (boundary : List (Fin input.val.wireCount))
    (sourceOuter : Fin (conversionSourceOpen input boundary).exposedWires.length → D)
    (targetOuter : Fin
      (conversionTargetOpen input node payload boundary).exposedWires.length → D)
    (sourceLocal : Fin
      (conversionSourceOpen input boundary).hiddenWires.length → D)
    (fallback : D)
    (outerEq : sourceOuter = targetOuter ∘ conversionExposedIndex boundary) :
    let hiddenLength := conversionTargetOpen_hidden_length
      (input := input) (node := node) (payload := payload) boundary
    let targetLocal : Fin
        (conversionTargetOpen input node payload boundary).hiddenWires.length → D :=
      fun index => Fin.addCases sourceLocal (fun _ => fallback)
        (Fin.cast hiddenLength index)
    Diagram.ConcreteElaboration.rootEnvironment
        (conversionSourceOpen input boundary).exposedWires
        (conversionSourceOpen input boundary).hiddenWires sourceOuter sourceLocal =
      Diagram.ConcreteElaboration.rootEnvironment
          (conversionTargetOpen input node payload boundary).exposedWires
          (conversionTargetOpen input node payload boundary).hiddenWires
          targetOuter targetLocal ∘ conversionRootIndex boundary := by
  dsimp only
  funext index
  unfold Diagram.ConcreteElaboration.rootEnvironment
  let split : Fin ((conversionSourceOpen input boundary).exposedWires.length +
      (conversionSourceOpen input boundary).hiddenWires.length) :=
    Fin.cast List.length_append index
  have recover : Fin.cast List.length_append.symm split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · rw [outerEq]
    simp only [Function.comp_apply]
    simp [Diagram.extendWireEnv]
    change targetOuter (conversionExposedIndex boundary outer) =
      Diagram.extendWireEnv targetOuter _
        (Fin.cast List.length_append
          (conversionRootIndex boundary
            (Fin.cast List.length_append.symm
              (Fin.castAdd
                (conversionSourceOpen input boundary).hiddenWires.length
                outer))))
    have targetIndexEq :
        Fin.cast List.length_append
            (conversionRootIndex boundary
              (Fin.cast List.length_append.symm
                (Fin.castAdd
                  (conversionSourceOpen input boundary).hiddenWires.length
                  outer))) =
          Fin.castAdd
            (conversionTargetOpen input node payload boundary).hiddenWires.length
            (conversionExposedIndex boundary outer) := by
      apply Fin.ext
      rfl
    rw [targetIndexEq]
    simp [Diagram.extendWireEnv]
  · simp only [Function.comp_apply]
    simp [Diagram.extendWireEnv]
    change sourceLocal localIndex =
      Diagram.extendWireEnv targetOuter _
        (Fin.cast List.length_append
          (conversionRootIndex boundary
            (Fin.cast List.length_append.symm
              (Fin.natAdd
                (conversionSourceOpen input boundary).exposedWires.length
                localIndex))))
    have targetIndexEq :
        Fin.cast List.length_append
            (conversionRootIndex boundary
              (Fin.cast List.length_append.symm
                (Fin.natAdd
                  (conversionSourceOpen input boundary).exposedWires.length
                  localIndex))) =
          Fin.natAdd
            (conversionTargetOpen input node payload boundary).exposedWires.length
            (Fin.cast
              (conversionTargetOpen_hidden_length
                (input := input) (node := node) (payload := payload)
                boundary).symm
              (Fin.castAdd (conversionRootFresh input node payload).length
                localIndex)) := by
      apply Fin.ext
      change (conversionSourceOpen input boundary).exposedWires.length +
          localIndex.val =
        (conversionTargetOpen input node payload boundary).exposedWires.length +
          localIndex.val
      rw [conversionTargetOpen_exposed_length]
    rw [targetIndexEq]
    simp [Diagram.extendWireEnv]

private theorem conversionRootEnvironment_backward
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    {D : Type}
    (boundary : List (Fin input.val.wireCount))
    (sourceOuter : Fin (conversionSourceOpen input boundary).exposedWires.length → D)
    (targetOuter : Fin
      (conversionTargetOpen input node payload boundary).exposedWires.length → D)
    (targetLocal : Fin
      (conversionTargetOpen input node payload boundary).hiddenWires.length → D)
    (outerEq : sourceOuter = targetOuter ∘ conversionExposedIndex boundary) :
    let hiddenLength := conversionTargetOpen_hidden_length
      (input := input) (node := node) (payload := payload) boundary
    let sourceLocal : Fin
        (conversionSourceOpen input boundary).hiddenWires.length → D :=
      fun index => targetLocal
        (Fin.cast hiddenLength.symm
          (Fin.castAdd (conversionRootFresh input node payload).length index))
    Diagram.ConcreteElaboration.rootEnvironment
        (conversionSourceOpen input boundary).exposedWires
        (conversionSourceOpen input boundary).hiddenWires sourceOuter sourceLocal =
      Diagram.ConcreteElaboration.rootEnvironment
          (conversionTargetOpen input node payload boundary).exposedWires
          (conversionTargetOpen input node payload boundary).hiddenWires
          targetOuter targetLocal ∘ conversionRootIndex boundary := by
  dsimp only
  funext index
  unfold Diagram.ConcreteElaboration.rootEnvironment
  let split : Fin ((conversionSourceOpen input boundary).exposedWires.length +
      (conversionSourceOpen input boundary).hiddenWires.length) :=
    Fin.cast List.length_append index
  have recover : Fin.cast List.length_append.symm split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · rw [outerEq]
    simp only [Function.comp_apply]
    simp [Diagram.extendWireEnv]
    change targetOuter (conversionExposedIndex boundary outer) =
      Diagram.extendWireEnv targetOuter targetLocal
        (Fin.cast List.length_append
          (conversionRootIndex boundary
            (Fin.cast List.length_append.symm
              (Fin.castAdd
                (conversionSourceOpen input boundary).hiddenWires.length
                outer))))
    have targetIndexEq :
        Fin.cast List.length_append
            (conversionRootIndex boundary
              (Fin.cast List.length_append.symm
                (Fin.castAdd
                  (conversionSourceOpen input boundary).hiddenWires.length
                  outer))) =
          Fin.castAdd
            (conversionTargetOpen input node payload boundary).hiddenWires.length
            (conversionExposedIndex boundary outer) := by
      apply Fin.ext
      rfl
    rw [targetIndexEq]
    simp [Diagram.extendWireEnv]
  · simp only [Function.comp_apply]
    simp [Diagram.extendWireEnv]
    change targetLocal
        (Fin.cast
          (conversionTargetOpen_hidden_length
            (input := input) (node := node) (payload := payload) boundary).symm
          (Fin.castAdd (conversionRootFresh input node payload).length
            localIndex)) =
      Diagram.extendWireEnv targetOuter targetLocal
        (Fin.cast List.length_append
          (conversionRootIndex boundary
            (Fin.cast List.length_append.symm
              (Fin.natAdd
                (conversionSourceOpen input boundary).exposedWires.length
                localIndex))))
    have targetIndexEq :
        Fin.cast List.length_append
            (conversionRootIndex boundary
              (Fin.cast List.length_append.symm
                (Fin.natAdd
                  (conversionSourceOpen input boundary).exposedWires.length
                  localIndex))) =
          Fin.natAdd
            (conversionTargetOpen input node payload boundary).exposedWires.length
            (Fin.cast
              (conversionTargetOpen_hidden_length
                (input := input) (node := node) (payload := payload)
                boundary).symm
              (Fin.castAdd (conversionRootFresh input node payload).length
                localIndex)) := by
      apply Fin.ext
      change (conversionSourceOpen input boundary).exposedWires.length +
          localIndex.val =
        (conversionTargetOpen input node payload boundary).exposedWires.length +
          localIndex.val
      rw [conversionTargetOpen_exposed_length]
    rw [targetIndexEq]
    simp [Diagram.extendWireEnv]

private noncomputable def conversionRaw_extendedWireMapOfNe
    (embedding : ConversionContextEmbedding input node payload source target)
    (region : Fin input.val.regionCount) (hne : region ≠ payload.region) :
    Fin (source.extend region).length → Fin (target.extend region).length :=
  fun index =>
    Fin.cast
      ((congrArg (fun localCount => target.length + localCount)
          (conversionRaw_exactScopeWires_length_of_ne region hne).symm).trans
        (Diagram.ConcreteElaboration.WireContext.length_extend target region).symm)
      (Diagram.extendWireRenaming embedding.index
        (Diagram.ConcreteElaboration.exactScopeWires input.val region).length
        (Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend source region)
          index))

private theorem conversionRaw_extendedWireMapOfNe_spec
    (embedding : ConversionContextEmbedding input node payload source target)
    (region : Fin input.val.regionCount) (hne : region ≠ payload.region)
    (index : Fin (source.extend region).length) :
    (target.extend region).get
        (conversionRaw_extendedWireMapOfNe embedding region hne index) =
      Fin.castAdd payload.freshPorts.length
        ((source.extend region).get index) := by
  let split := Fin.cast
    (Diagram.ConcreteElaboration.WireContext.length_extend source region) index
  have hrecover : Fin.cast
      (Diagram.ConcreteElaboration.WireContext.length_extend source region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have hmap : conversionRaw_extendedWireMapOfNe embedding region hne
        (Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend source region).symm
          (Fin.castAdd
            (Diagram.ConcreteElaboration.exactScopeWires input.val region).length
            outer)) =
        Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.castAdd
            (Diagram.ConcreteElaboration.exactScopeWires
              (conversionRaw input node payload) region).length
            (embedding.index outer)) := by
      apply Fin.ext
      simp [conversionRaw_extendedWireMapOfNe, Diagram.extendWireRenaming]
    rw [hmap]
    simpa [Diagram.ConcreteElaboration.WireContext.extend] using
      embedding.get outer
  · let hlength := conversionRaw_exactScopeWires_length_of_ne
      (input := input) (node := node) (payload := payload) region hne
    have hmap : conversionRaw_extendedWireMapOfNe embedding region hne
        (Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend source region).symm
          (Fin.natAdd source.length localIndex)) =
        Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.natAdd target.length (Fin.cast hlength.symm localIndex)) := by
      apply Fin.ext
      simp [conversionRaw_extendedWireMapOfNe, Diagram.extendWireRenaming]
    rw [hmap]
    have hlist := conversionRaw_exactScopeWires
      (input := input) (node := node) (payload := payload) region
    rw [if_neg hne] at hlist
    simp only [List.append_nil] at hlist
    simp [Diagram.ConcreteElaboration.WireContext.extend, hlist]
    exact List.getElem_map _

private theorem ConversionContextEmbedding.extend_index_eq_map_of_ne
    (embedding : ConversionContextEmbedding input node payload source target)
    (region : Fin input.val.regionCount) (hne : region ≠ payload.region)
    (targetNodup : (target.extend region).Nodup)
    (index : Fin (source.extend region).length) :
    (embedding.extend region).index index =
      conversionRaw_extendedWireMapOfNe embedding region hne index := by
  symm
  apply ConversionContextEmbedding.index_eq_of_get
    (embedding.extend region) targetNodup index
  exact conversionRaw_extendedWireMapOfNe_spec embedding region hne index

private theorem conversionRaw_extendWireEnv_of_ne
    (embedding : ConversionContextEmbedding input node payload source target)
    (region : Fin input.val.regionCount) (hne : region ≠ payload.region)
    (outerEnv : Fin target.length → D)
    (localEnv : Fin (Diagram.ConcreteElaboration.exactScopeWires
      (conversionRaw input node payload) region).length → D) :
    (Diagram.extendWireEnv outerEnv localEnv ∘
        Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend target region)) ∘
        conversionRaw_extendedWireMapOfNe embedding region hne =
      Diagram.extendWireEnv (outerEnv ∘ embedding.index)
          (localEnv ∘ Fin.cast
            (conversionRaw_exactScopeWires_length_of_ne region hne).symm) ∘
        Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend source region) := by
  funext wire
  let split := Fin.cast
    (Diagram.ConcreteElaboration.WireContext.length_extend source region) wire
  have hrecover : Fin.cast
      (Diagram.ConcreteElaboration.WireContext.length_extend source region).symm
      split = wire := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localWire => ?_) split
  · simp [conversionRaw_extendedWireMapOfNe, Diagram.extendWireEnv,
      Diagram.extendWireRenaming, Function.comp_def]
  · simp [conversionRaw_extendedWireMapOfNe, Diagram.extendWireEnv,
      Diagram.extendWireRenaming, Function.comp_def]
    rw [show Fin.cast _ (Fin.natAdd target.length localWire) =
        Fin.natAdd target.length
          (Fin.cast
            (conversionRaw_exactScopeWires_length_of_ne region hne).symm
            localWire) by
      apply Fin.ext
      rfl]
    exact Fin.addCases_right _

private theorem conversionRaw_exactScopeWires_length_at_region :
    (Diagram.ConcreteElaboration.exactScopeWires
      (conversionRaw input node payload) payload.region).length =
      (Diagram.ConcreteElaboration.exactScopeWires
        input.val payload.region).length + payload.freshPorts.length := by
  rw [conversionRaw_exactScopeWires]
  simp only [VisualProof.Data.Finite.allFin_eq_finRange]
  calc
    (List.map (Fin.castAdd payload.freshPorts.length)
          (Diagram.ConcreteElaboration.exactScopeWires input.val payload.region) ++
        List.map (Fin.natAdd input.val.wireCount)
          (List.finRange payload.freshPorts.length)).length =
        (Diagram.ConcreteElaboration.exactScopeWires
          input.val payload.region).length +
          (List.finRange payload.freshPorts.length).length := by
            rw [List.length_append, List.length_map, List.length_map]
    _ = (Diagram.ConcreteElaboration.exactScopeWires
          input.val payload.region).length + payload.freshPorts.length := by simp

private noncomputable def conversionRaw_extendedWireMapAtRegion
    (embedding : ConversionContextEmbedding input node payload source target) :
    Fin (source.extend payload.region).length →
      Fin (target.extend payload.region).length :=
  fun index =>
    Fin.cast
      (Diagram.ConcreteElaboration.WireContext.length_extend
        target payload.region).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (Diagram.ConcreteElaboration.exactScopeWires
            (conversionRaw input node payload) payload.region).length
          (embedding.index outer))
        (fun localIndex => Fin.natAdd target.length
          (Fin.cast conversionRaw_exactScopeWires_length_at_region.symm
            (Fin.castAdd payload.freshPorts.length localIndex)))
        (Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend
            source payload.region) index))

private theorem conversionRaw_extendedWireMapAtRegion_spec
    (embedding : ConversionContextEmbedding input node payload source target)
    (index : Fin (source.extend payload.region).length) :
    (target.extend payload.region).get
        (conversionRaw_extendedWireMapAtRegion embedding index) =
      Fin.castAdd payload.freshPorts.length
        ((source.extend payload.region).get index) := by
  let split := Fin.cast
    (Diagram.ConcreteElaboration.WireContext.length_extend source payload.region)
    index
  have hrecover : Fin.cast
      (Diagram.ConcreteElaboration.WireContext.length_extend
        source payload.region).symm split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have hmap : conversionRaw_extendedWireMapAtRegion embedding
        (Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend
            source payload.region).symm
          (Fin.castAdd
            (Diagram.ConcreteElaboration.exactScopeWires
              input.val payload.region).length outer)) =
        Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend
            target payload.region).symm
          (Fin.castAdd
            (Diagram.ConcreteElaboration.exactScopeWires
              (conversionRaw input node payload) payload.region).length
            (embedding.index outer)) := by
      apply Fin.ext
      simp [conversionRaw_extendedWireMapAtRegion]
    rw [hmap]
    simpa [Diagram.ConcreteElaboration.WireContext.extend] using
      embedding.get outer
  · let hlength := conversionRaw_exactScopeWires_length_at_region
      (input := input) (node := node) (payload := payload)
    have hmap : conversionRaw_extendedWireMapAtRegion embedding
        (Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend
            source payload.region).symm
          (Fin.natAdd source.length localIndex)) =
        Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend
            target payload.region).symm
          (Fin.natAdd target.length
            (Fin.cast hlength.symm
              (Fin.castAdd payload.freshPorts.length localIndex))) := by
      apply Fin.ext
      simp [conversionRaw_extendedWireMapAtRegion]
    rw [hmap]
    have hlist := conversionRaw_exactScopeWires
      (input := input) (node := node) (payload := payload) payload.region
    simp [Diagram.ConcreteElaboration.WireContext.extend, hlist]
    change (List.map (Fin.castAdd payload.freshPorts.length)
      (Diagram.ConcreteElaboration.exactScopeWires input.val payload.region) ++
      List.map (Fin.natAdd input.val.wireCount)
        (VisualProof.Data.Finite.allFin payload.freshPorts.length))[localIndex.val] =
        Fin.castAdd payload.freshPorts.length
          (Diagram.ConcreteElaboration.exactScopeWires
            input.val payload.region)[localIndex.val]
    rw [List.getElem_append_left (by
      rw [List.length_map]
      exact localIndex.isLt)]
    exact List.getElem_map _

private theorem ConversionContextEmbedding.extend_index_eq_map_at_region
    (embedding : ConversionContextEmbedding input node payload source target)
    (targetNodup : (target.extend payload.region).Nodup)
    (index : Fin (source.extend payload.region).length) :
    (embedding.extend payload.region).index index =
      conversionRaw_extendedWireMapAtRegion embedding index := by
  symm
  apply ConversionContextEmbedding.index_eq_of_get
    (embedding.extend payload.region) targetNodup index
  exact conversionRaw_extendedWireMapAtRegion_spec embedding index

private theorem conversionRaw_extendWireEnv_at_region
    (embedding : ConversionContextEmbedding input node payload source target)
    (outerEnv : Fin target.length → D)
    (localEnv : Fin (Diagram.ConcreteElaboration.exactScopeWires
      (conversionRaw input node payload) payload.region).length → D) :
    (Diagram.extendWireEnv outerEnv localEnv ∘
        Fin.cast (Diagram.ConcreteElaboration.WireContext.length_extend
          target payload.region)) ∘
        conversionRaw_extendedWireMapAtRegion embedding =
      Diagram.extendWireEnv (outerEnv ∘ embedding.index)
          (fun localWire => localEnv
            (Fin.cast conversionRaw_exactScopeWires_length_at_region.symm
              (Fin.castAdd payload.freshPorts.length localWire))) ∘
        Fin.cast (Diagram.ConcreteElaboration.WireContext.length_extend
          source payload.region) := by
  funext wire
  let split := Fin.cast
    (Diagram.ConcreteElaboration.WireContext.length_extend source payload.region)
    wire
  have hrecover : Fin.cast
      (Diagram.ConcreteElaboration.WireContext.length_extend
        source payload.region).symm split = wire := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localWire => ?_) split
  · simp [conversionRaw_extendedWireMapAtRegion, Diagram.extendWireEnv,
      Function.comp_def]
  · simp [conversionRaw_extendedWireMapAtRegion, Diagram.extendWireEnv,
      Function.comp_def]

private theorem conversionRaw_node_region
    (candidate : Fin input.val.nodeCount) :
    ((conversionRaw input node payload).nodes candidate).region =
      (input.val.nodes candidate).region := by
  by_cases heq : candidate = node
  · subst candidate
    change (if node = node then
      (Diagram.CNode.term payload.region payload.newFreePorts payload.newTerm)
      else input.val.nodes node).region = (input.val.nodes node).region
    rw [if_pos rfl, payload.node_eq]
    rfl
  · simp [conversionRaw, heq]

private theorem conversionRaw_localOccurrences
    (region : Fin input.val.regionCount) :
    Diagram.ConcreteElaboration.localOccurrences
        (conversionRaw input node payload) region =
      Diagram.ConcreteElaboration.localOccurrences input.val region := by
  unfold Diagram.ConcreteElaboration.localOccurrences
  have hpred :
      (fun candidate : Fin input.val.nodeCount =>
        decide (((conversionRaw input node payload).nodes candidate).region =
          region)) =
      (fun candidate : Fin input.val.nodeCount =>
        decide ((input.val.nodes candidate).region = region)) := by
    funext candidate
    rw [conversionRaw_node_region]
    rfl
  have hnodes' :
      VisualProof.Data.Finite.filterFin (fun candidate : Fin input.val.nodeCount =>
        decide (((conversionRaw input node payload).nodes candidate).region =
          region)) =
      VisualProof.Data.Finite.filterFin (fun candidate : Fin input.val.nodeCount =>
        decide ((input.val.nodes candidate).region = region)) :=
    congrArg VisualProof.Data.Finite.filterFin hpred
  have hmapped := congrArg
    (List.map (fun candidate =>
      Diagram.ConcreteElaboration.LocalOccurrence.node
        (regions := input.val.regionCount) candidate)) hnodes'
  exact Eq.trans (congrArg (fun nodes => nodes ++
    (VisualProof.Data.Finite.filterFin fun child : Fin input.val.regionCount =>
      decide (((conversionRaw input node payload).regions child).parent? =
        some region)).map
          (fun child => Diagram.ConcreteElaboration.LocalOccurrence.child
            (nodes := input.val.nodeCount) child)) hmapped) rfl

private theorem conversionRaw_localSelection
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (direction : Diagram.ConcreteElaboration.SimulationDirection)
    (source : Diagram.ConcreteElaboration.WireContext input.val)
    (target : Diagram.ConcreteElaboration.WireContext
      (conversionRaw input node payload))
    (embedding : ConversionContextEmbedding input node payload source target)
    (region : Fin input.val.regionCount)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region)
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin source.length → model.Carrier)
      (targetOuter : Fin target.length → model.Carrier),
      Diagram.ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
          (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
            embedding.index)
          sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal : Fin
            (Diagram.ConcreteElaboration.exactScopeWires input.val region).length →
              model.Carrier,
            ∃ targetLocal : Fin (Diagram.ConcreteElaboration.exactScopeWires
                (conversionRaw input node payload) region).length →
                model.Carrier,
              (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
                (embedding.extend region).index).EnvironmentsAgree
                (Diagram.ConcreteElaboration.extendedEnvironment source region
                  sourceOuter sourceLocal)
                (Diagram.ConcreteElaboration.extendedEnvironment target region
                  targetOuter targetLocal)
        | .backward => ∀ targetLocal : Fin
            (Diagram.ConcreteElaboration.exactScopeWires
              (conversionRaw input node payload) region).length → model.Carrier,
            ∃ sourceLocal : Fin
                (Diagram.ConcreteElaboration.exactScopeWires input.val region).length →
                model.Carrier,
              (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
                (embedding.extend region).index).EnvironmentsAgree
                (Diagram.ConcreteElaboration.extendedEnvironment source region
                  sourceOuter sourceLocal)
                (Diagram.ConcreteElaboration.extendedEnvironment target region
                  targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgrees
  have outerEq : sourceOuter = targetOuter ∘ embedding.index :=
    (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceOuter targetOuter).mp
      outerAgrees
  let fallback : model.Carrier :=
    model.eval (Lambda.Term.lam (Lambda.Term.bvar 0) :
      Lambda.Term 0 (Fin 0)) Fin.elim0
  cases direction with
  | forward =>
      intro sourceLocal
      by_cases hsite : region = payload.region
      · subst region
        let targetLocal : Fin (Diagram.ConcreteElaboration.exactScopeWires
            (conversionRaw input node payload) payload.region).length →
            model.Carrier :=
          fun index => Fin.addCases sourceLocal (fun _ => fallback)
            (Fin.cast conversionRaw_exactScopeWires_length_at_region index)
        refine ⟨targetLocal, ?_⟩
        apply (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          (embedding.extend payload.region).index
            _ _).mpr
        have hlocal :
            (fun localWire => targetLocal
              (Fin.cast conversionRaw_exactScopeWires_length_at_region.symm
                (Fin.castAdd payload.freshPorts.length localWire))) =
              sourceLocal := by
          funext localWire
          simp [targetLocal, fallback]
        have henv := conversionRaw_extendWireEnv_at_region
          (D := model.Carrier) embedding targetOuter targetLocal
        have hindex : (embedding.extend payload.region).index =
            conversionRaw_extendedWireMapAtRegion embedding := by
          funext index
          exact embedding.extend_index_eq_map_at_region targetExact.nodup index
        unfold Diagram.ConcreteElaboration.extendedEnvironment
        rw [hindex, henv, hlocal, outerEq]
      · let hlength := conversionRaw_exactScopeWires_length_of_ne
          (input := input) (node := node) (payload := payload) region hsite
        let targetLocal : Fin (Diagram.ConcreteElaboration.exactScopeWires
            (conversionRaw input node payload) region).length → model.Carrier :=
          sourceLocal ∘ Fin.cast hlength
        refine ⟨targetLocal, ?_⟩
        apply (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          (embedding.extend region).index _ _).mpr
        have hlocal : targetLocal ∘ Fin.cast hlength.symm = sourceLocal := by
          funext localWire
          simp [targetLocal]
        have henv := conversionRaw_extendWireEnv_of_ne
          (D := model.Carrier) embedding region hsite targetOuter targetLocal
        have hindex : (embedding.extend region).index =
            conversionRaw_extendedWireMapOfNe embedding region hsite := by
          funext index
          exact embedding.extend_index_eq_map_of_ne region hsite
            targetExact.nodup index
        unfold Diagram.ConcreteElaboration.extendedEnvironment
        rw [hindex, henv, hlocal, outerEq]
  | backward =>
      intro targetLocal
      by_cases hsite : region = payload.region
      · subst region
        let sourceLocal : Fin (Diagram.ConcreteElaboration.exactScopeWires
            input.val payload.region).length → model.Carrier := fun localWire =>
          targetLocal
            (Fin.cast conversionRaw_exactScopeWires_length_at_region.symm
              (Fin.castAdd payload.freshPorts.length localWire))
        refine ⟨sourceLocal, ?_⟩
        apply (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          (embedding.extend payload.region).index
            _ _).mpr
        have henv := conversionRaw_extendWireEnv_at_region
          (D := model.Carrier) embedding targetOuter targetLocal
        have hindex : (embedding.extend payload.region).index =
            conversionRaw_extendedWireMapAtRegion embedding := by
          funext index
          exact embedding.extend_index_eq_map_at_region targetExact.nodup index
        unfold Diagram.ConcreteElaboration.extendedEnvironment
        rw [hindex, henv, outerEq]
      · let hlength := conversionRaw_exactScopeWires_length_of_ne
          (input := input) (node := node) (payload := payload) region hsite
        let sourceLocal : Fin (Diagram.ConcreteElaboration.exactScopeWires
            input.val region).length → model.Carrier :=
          targetLocal ∘ Fin.cast hlength.symm
        refine ⟨sourceLocal, ?_⟩
        apply (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          (embedding.extend region).index _ _).mpr
        have henv := conversionRaw_extendWireEnv_of_ne
          (D := model.Carrier) embedding region hsite targetOuter targetLocal
        have hindex : (embedding.extend region).index =
            conversionRaw_extendedWireMapOfNe embedding region hsite := by
          funext index
          exact embedding.extend_index_eq_map_of_ne region hsite
            targetExact.nodup index
        unfold Diagram.ConcreteElaboration.extendedEnvironment
        rw [hindex, henv, outerEq]

private noncomputable def conversionSimulation
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (model : Lambda.LambdaModel)
    (named : Diagram.NamedEnv model.Carrier signature)
    (htarget : (conversionRaw input node payload).WellFormed signature) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation signature input.val
      (conversionRaw input node payload) model named where
  source_wellFormed := input.property
  target_wellFormed := htarget
  regionMap := id
  binderMap := id
  Distinguished := fun _ => False
  occurrenceMap := fun _ _ occurrence => occurrence
  occurrenceMap_node := by
    intro region regular candidate hregion
    exact ⟨candidate, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := rfl
  region_shape := by
    intro parent regular child hparent
    cases hkind : input.val.regions child <;> simp [conversionRaw, hkind]
  localOccurrences_map := by
    intro region regular
    change Diagram.ConcreteElaboration.localOccurrences
        (conversionRaw input node payload) region = _
    rw [conversionRaw_localOccurrences
      (input := input) (node := node) (payload := payload) region]
    have mapSelf : ∀ occurrences : List
        (Diagram.ConcreteElaboration.LocalOccurrence input.val.regionCount
          input.val.nodeCount),
        occurrences.map (fun occurrence => occurrence) = occurrences := by
      intro occurrences
      induction occurrences with
      | nil => rfl
      | cons head tail induction =>
          simp only [List.map_cons]
          rw [induction]
    exact (mapSelf _).symm
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    Diagram.ConcreteElaboration.IdentityBinderWitness
      (sourceRels := sourceRels) (targetRels := targetRels)
      input.val (conversionRaw input node payload) sourceBinders targetBinders
  relationMap := fun witness =>
    Diagram.ConcreteElaboration.IdentityBinderWitness.relationMap witness
  binders_empty := {
    relationContexts_eq := rfl
    binders_eq := HEq.rfl
  }
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    exact ⟨rfl, HEq.rfl⟩
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simpa [Diagram.ConcreteElaboration.IdentityBinderWitness.relationMap,
      Diagram.ConcreteElaboration.identityRelationRenaming] using
        (Diagram.RelationRenaming.lift_id_fun
          (source := sourceRels) arity).symm
  Allowed := fun _ _ => True
  allowed_cut := by simp
  allowed_bubble := by simp
  ContextWitness := ConversionContextEmbedding input node payload
  AtRegion := fun _ _ => True
  indexRelation := fun embedding =>
    Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index
  extendContext := fun source target embedding region _regular sourceExact targetExact =>
    embedding.extend region
  extendFocusedContext := by
    intro source target embedding region focused sourceExact targetExact
    exact False.elim focused
  at_child := by simp
  at_extended := by simp
  at_focused_child := by
    intro source target embedding parent focused sourceExact targetExact child
      atParent sourceParent targetParent
    exact False.elim focused
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget source target
      embedding sourceBinders targetBinders binderWitness region atRegion regular
      allowed sourceExact targetExact _ _ _ _ sourceItems targetItems
      sourceCompiled targetCompiled itemSemantics
    exact Diagram.ConcreteElaboration.directionalLocalTransport_of_agreement
      direction source target region region
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
        (embedding.extend region).index)
      model named
      (sourceItems.renameRelations
        (Diagram.ConcreteElaboration.IdentityBinderWitness.relationMap
          binderWitness))
      targetItems
      (conversionRaw_localSelection direction source target embedding region
        sourceExact targetExact model)
      itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region source target embedding
      atRegion sourceNodup targetNodup sourceBinders targetBinders allowed
      binderWitness sourceNode targetNode
      regular mapped nodeRegion sourceItem targetItem sourceCompiled targetCompiled
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    change Diagram.ConcreteElaboration.ItemSimulation model named direction
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      (sourceItem.renameRelations
        ((fun relation => relation) :
          Diagram.RelationRenaming sourceRels sourceRels))
      targetItem
    rw [Diagram.Item.renameRelations_id]
    have targetNodeEq : targetNode = sourceNode := by
      exact Diagram.ConcreteElaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    intro sourceEnv targetEnv relEnv environments
    have environmentEq : sourceEnv = targetEnv ∘ embedding.index :=
      (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        embedding.index sourceEnv targetEnv).mp
        environments
    rw [environmentEq]
    by_cases converted : sourceNode = node
    · subst sourceNode
      have semantic := conversionRaw_compileNode_denote_iff source target
        embedding sourceBinders targetNodup htarget.wire_endpoints_are_disjoint
        sourceItem targetItem sourceCompiled targetCompiled model named targetEnv
        relEnv
      cases direction with
      | forward => exact semantic.mp
      | backward => exact semantic.mpr
    · have mappedCompile := conversionRaw_compileNode?_other source target
        embedding sourceBinders targetNodup htarget.wire_endpoints_are_disjoint
        sourceNode converted
      rw [sourceCompiled] at mappedCompile
      simp only [Option.map_some] at mappedCompile
      rw [targetCompiled] at mappedCompile
      have itemEq : targetItem = sourceItem.renameWires embedding.index :=
        Option.some.inj mappedCompile
      subst targetItem
      have semantic := Diagram.denoteItem_renameWires model named embedding.index
        targetEnv relEnv sourceItem
      cases direction with
      | forward => exact semantic.mpr
      | backward => exact semantic.mp
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region source
      target embedding sourceBinders targetBinders atRegion distinguished
    exact False.elim distinguished

private noncomputable def conversionRootContext
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire : Fin input.val.wireCount, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (htarget : (conversionRaw input node payload).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : Diagram.NamedEnv model.Carrier signature)
    (direction : Diagram.ConcreteElaboration.SimulationDirection) :
    let simulation := conversionSimulation model named htarget
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction
      (conversionSourceOpen input boundary).exposedWires
      (conversionSourceOpen input boundary).hiddenWires
      (conversionTargetOpen input node payload boundary).exposedWires
      (conversionTargetOpen input node payload boundary).hiddenWires := by
  let simulation := conversionSimulation model named htarget
  let embedding := conversionRootEmbedding boundary sourceRoot htarget
  refine {
    outer := Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
      (conversionExposedIndex boundary)
    context := ?_
    atRoot := True.intro
    atRootChild := by
      intro regular child parent
      trivial
    atFocusedRootChild := by
      intro focused
      exact False.elim focused
    transport := ?_
    focusedRootKernel := ?_
  }
  · simpa only [Diagram.OpenConcreteDiagram.rootWires] using embedding
  · intro regular allowed sourceItems targetItems sourceCompiled targetCompiled
      itemSemantics
    refine Diagram.ConcreteElaboration.directionalRootTransport_of_agreement
      direction
      (conversionSourceOpen input boundary).exposedWires
      (conversionSourceOpen input boundary).hiddenWires
      (conversionTargetOpen input node payload boundary).exposedWires
      (conversionTargetOpen input node payload boundary).hiddenWires
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
        (conversionExposedIndex boundary))
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      model named
      (sourceItems.renameRelations
        ((conversionSimulation model named htarget).relationMap
          (conversionSimulation model named htarget).binders_empty))
      targetItems ?_ itemSemantics
    intro sourceOuter targetOuter outerAgrees
    rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
      at outerAgrees
    have indexEq : embedding.index = conversionRootIndex boundary := by
      funext index
      exact conversionRootEmbedding_index boundary sourceRoot htarget index
    cases direction with
    | forward =>
        intro sourceLocal
        let fallback : model.Carrier :=
          model.eval (Lambda.Term.lam (Lambda.Term.bvar 0) :
            Lambda.Term 0 (Fin 0)) Fin.elim0
        let hiddenLength := conversionTargetOpen_hidden_length
          (input := input) (node := node) (payload := payload) boundary
        let targetLocal : Fin
            (conversionTargetOpen input node payload boundary).hiddenWires.length →
            model.Carrier := fun index =>
          Fin.addCases sourceLocal (fun _ => fallback)
            (Fin.cast hiddenLength index)
        refine ⟨targetLocal, ?_⟩
        apply (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          embedding.index _ _).2
        rw [indexEq]
        exact conversionRootEnvironment_forward boundary sourceOuter targetOuter
          sourceLocal fallback outerAgrees
    | backward =>
        intro targetLocal
        let hiddenLength := conversionTargetOpen_hidden_length
          (input := input) (node := node) (payload := payload) boundary
        let sourceLocal : Fin
            (conversionSourceOpen input boundary).hiddenWires.length →
            model.Carrier := fun index =>
          targetLocal
            (Fin.cast hiddenLength.symm
              (Fin.castAdd (conversionRootFresh input node payload).length index))
        refine ⟨sourceLocal, ?_⟩
        apply (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          embedding.index _ _).2
        rw [indexEq]
        exact conversionRootEnvironment_backward boundary sourceOuter targetOuter
          targetLocal outerAgrees
  · intro atRoot distinguished
    exact False.elim distinguished

private theorem conversionBoundaryWitness
    {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : ConversionPayload input node}
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire : Fin input.val.wireCount, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (htarget : (conversionRaw input node payload).WellFormed signature)
    (direction : Diagram.ConcreteElaboration.SimulationDirection)
    (model : Lambda.LambdaModel)
    (named : Diagram.NamedEnv model.Carrier signature)
    (sourceArgs : Fin boundary.length → model.Carrier) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction
      (conversionSourceCheckedOpen input boundary sourceRoot).elaborate
      (conversionTargetCheckedOpen input node payload boundary sourceRoot
        htarget).elaborate
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
        (conversionExposedIndex boundary))
      model named sourceArgs
      (sourceArgs ∘ Fin.cast (conversionBoundaryLengthEq boundary)) := by
  cases direction with
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      let targetAssignment : Diagram.BoundaryAssignment
          (conversionTargetCheckedOpen input node payload boundary sourceRoot
            htarget).elaborate model.Carrier := {
        args := sourceArgs ∘ Fin.cast (conversionBoundaryLengthEq boundary)
        classes := sourceAssignment.classes ∘
          conversionSourceExposedIndex boundary
        agrees := by
          intro targetPosition
          let sourcePosition := Fin.cast (conversionBoundaryLengthEq boundary)
            targetPosition
          have classEq := conversionBoundaryClass
            (input := input) (node := node) (payload := payload) boundary
            sourcePosition
          have positionEq : Fin.cast (conversionBoundaryLengthEq boundary).symm
              sourcePosition = targetPosition := by
            apply Fin.ext
            rfl
          rw [positionEq] at classEq
          change sourceAssignment.classes
              (conversionSourceExposedIndex boundary
                ((conversionTargetOpen input node payload boundary).boundaryClass
                  targetPosition)) = sourceArgs sourcePosition
          rw [← classEq, conversionSourceExposedIndex_exposedIndex]
          have sourceAgrees := sourceAssignment.agrees sourcePosition
          change sourceAssignment.classes
              ((conversionSourceOpen input boundary).boundaryClass sourcePosition) =
            sourceAssignment.args sourcePosition at sourceAgrees
          rw [sourceArgsEq] at sourceAgrees
          exact sourceAgrees
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      apply (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).2
      funext sourceClass
      simp only [targetAssignment, Function.comp_apply]
      rw [conversionSourceExposedIndex_exposedIndex]
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      let sourceAssignment : Diagram.BoundaryAssignment
          (conversionSourceCheckedOpen input boundary sourceRoot).elaborate
          model.Carrier := {
        args := sourceArgs
        classes := targetAssignment.classes ∘ conversionExposedIndex boundary
        agrees := by
          intro sourcePosition
          change targetAssignment.classes
              (conversionExposedIndex boundary
                ((conversionSourceOpen input boundary).boundaryClass
                  sourcePosition)) = sourceArgs sourcePosition
          rw [conversionBoundaryClass]
          have targetAgrees := targetAssignment.agrees
            (Fin.cast (conversionBoundaryLengthEq boundary).symm sourcePosition)
          rw [targetArgsEq] at targetAgrees
          exact targetAgrees
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      apply (Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).2
      rfl

/-- Every successful conversion receipt preserves denotation at every ordered
open boundary, in both replay orientations. -/
theorem applyConversion_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (payload : ConversionPayload input node)
    (receipt : StepReceipt input)
    (happly : applyConversion input node payload = .ok receipt) :
    SuccessfulReceiptSound context orientation input (.conversion node payload)
      receipt := by
  have realizes := applyConversion_realizes happly
  have targetWellFormed : (conversionRaw input node payload).WellFormed
      signature := realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      conversionOperationalOpen realizes boundary sourceRoot)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      conversionOperationalIso realizes boundary sourceRoot mapped htransport)
  intro boundary sourceRoot mapped htransport valid args
  let source := conversionSourceCheckedOpen input boundary sourceRoot
  let target := conversionTargetCheckedOpen input node payload boundary sourceRoot
    targetWellFormed
  let model := Lambda.canonicalModel
  let named := Theory.interpretDefinitions context.definitions
  let simulation := conversionSimulation model named targetWellFormed
  let targetArgs := args ∘ Fin.cast
    (conversionBoundaryLengthEq
      (input := input) (node := node) (payload := payload) boundary)
  have forwardAllowed : simulation.Allowed .forward input.val.root := by
    trivial
  have backwardAllowed : simulation.Allowed .backward input.val.root := by
    trivial
  have forwardSemantic :=
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source target model named simulation .forward
      (conversionRootContext boundary sourceRoot targetWellFormed model named
        .forward)
      forwardAllowed args targetArgs
      (conversionBoundaryWitness boundary sourceRoot targetWellFormed .forward
        model named args)
  have backwardSemantic :=
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source target model named simulation .backward
      (conversionRootContext boundary sourceRoot targetWellFormed model named
        .backward)
      backwardAllowed args targetArgs
      (conversionBoundaryWitness boundary sourceRoot targetWellFormed .backward
        model named args)
  dsimp only
  unfold DirectedEntailment
  constructor
  · intro sourceDenotes
    have targetDenotes := forwardSemantic sourceDenotes
    simpa [source, target, targetArgs, model, named, conversionSourceCheckedOpen,
      conversionTargetCheckedOpen, conversionOperationalOpen] using targetDenotes
  · intro targetDenotes
    apply backwardSemantic
    simpa [source, target, targetArgs, model, named, conversionSourceCheckedOpen,
      conversionTargetCheckedOpen, conversionOperationalOpen] using targetDenotes

/-- Every successful congruence-join receipt is semantically equivalent. -/
theorem applyCongruenceJoin_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (first second : Fin input.val.nodeCount)
    (payload : CongruencePayload input first second)
    (receipt : StepReceipt input)
    (happly : applyCongruenceJoin input payload = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.congruenceJoin first second payload) receipt := by
  exact CongruenceSoundness.applyCongruenceJoin_sound
    context orientation input first second payload receipt happly

/-- Every successful anchored-wire contraction receipt is equivalent. -/
theorem applyAnchoredWireContract_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (redundant survivor : Fin input.val.nodeCount)
    (certificate : Lambda.Certificate)
    (receipt : StepReceipt input)
    (happly :
      applyAnchoredWireContract input redundant survivor certificate =
        .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.anchoredWireContract redundant survivor certificate) receipt := by
  obtain ⟨redundantRegion, redundantTerm, survivorRegion, survivorTerm,
    drop, keep, _nodeDistinct, redundantShape, survivorShape,
    certificateAccepted, redundantOwner, survivorOwner, distinct, sameDepth,
    accepted, resultEq⟩ := applyAnchoredWireContract_success input redundant
      survivor certificate receipt happly
  obtain ⟨realizedDrop, realizedKeep, realizedRedundantOwner,
    realizedSurvivorOwner, realizes⟩ := applyAnchoredWireContract_realizes happly
  have dropEq : realizedDrop = drop := by
    rw [redundantOwner] at realizedRedundantOwner
    exact Option.some.inj realizedRedundantOwner.symm
  have keepEq : realizedKeep = keep := by
    rw [survivorOwner] at realizedSurvivorOwner
    exact Option.some.inj realizedSurvivorOwner.symm
  subst realizedDrop
  subst realizedKeep
  have redundantOccurs :=
    Diagram.ConcreteElaboration.endpointOwner?_sound redundantOwner
  have survivorOccurs :=
    Diagram.ConcreteElaboration.endpointOwner?_sound survivorOwner
  have endpointNodup :=
    AnchoredWireContractSoundness.movedEndpoints_nodup input redundant drop
  have sourceOccurs : ∀ endpoint,
      endpoint ∈ AnchoredWireContractSoundness.movedEndpoints input redundant drop →
        input.val.EndpointOccurs drop endpoint := fun endpoint member =>
    AnchoredWireContractSoundness.movedEndpoints_mem_occurs input redundant drop
      member
  have targetEncloses : ∀ endpoint,
      endpoint ∈ AnchoredWireContractSoundness.movedEndpoints input redundant drop →
        input.val.Encloses (input.val.wires keep).scope
          (input.val.nodes endpoint.node).region := by
    intro endpoint member
    exact (Classical.choice
      (AnchoredWireContractSoundness.movedEndpoint_availability input redundant
        drop keep survivorRegion accepted member)).wire_encloses_target
  have batchWellFormed :
      (AnchoredWireContractSoundness.moveEndpointsRaw input.val drop keep
        (AnchoredWireContractSoundness.movedEndpoints input redundant drop)
        ).WellFormed signature :=
    AnchoredWireContractSoundness.moveEndpointsRaw_wellFormed input.val
      input.property drop keep
      (AnchoredWireContractSoundness.movedEndpoints input redundant drop)
      distinct endpointNodup sourceOccurs targetEncloses
  have compactedWellFormed :
      (anchoredWireContractRaw input redundant drop keep).WellFormed signature := by
    rw [← resultEq]
    exact receipt.result.property
  have certificateEqual : ∀ model : Lambda.LambdaModel,
      model.eval redundantTerm Fin.elim0 =
        model.eval survivorTerm Fin.elim0 := fun model =>
    AnchoredWireContractSoundness.certified_closed_terms_equal redundantTerm
      survivorTerm certificate certificateAccepted model
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      ⟨realizes.rawResultOpen mapped,
        realizes.rawResultOpen_wellFormed sourceRoot htransport⟩)
    (operationalIso := fun _boundary _sourceRoot mapped _htransport =>
      Diagram.OpenConcreteIso.refl (realizes.rawResultOpen mapped))
  intro boundary sourceRoot mapped htransport valid args
  have rawTransport := realizes.transportBoundary_expected htransport
  have rawRoot :=
    (anchoredWireContractInterfaceTransport input redundant survivor drop keep
      ).transportBoundary_root_scoped sourceRoot rawTransport
  let rawMapped := realizes.targetBoundary mapped
  have sourceBatch :=
    AnchoredWireContractSoundness.contractionEndpointBatchOpen_denote_iff input
      redundant survivor redundantRegion survivorRegion redundantTerm survivorTerm
      drop keep certificate redundantShape survivorShape certificateAccepted
      redundantOwner survivorOwner distinct sameDepth accepted boundary sourceRoot
      Lambda.canonicalModel (Theory.interpretDefinitions context.definitions) args
  have compactedBatch :
      (AnchoredWireContractSoundness.anchoredContractCompactedOpen input redundant
        drop keep rawMapped).denote
          { diagram_well_formed := compactedWellFormed
            boundary_is_root_scoped := rawRoot }
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (args ∘ Fin.cast (by
            exact (anchoredWireContractInterfaceTransport input redundant
              survivor drop keep).transportBoundary_length rawTransport)) ↔
        (AnchoredWireContractSoundness.anchoredContractBatchOpen input redundant
          drop keep boundary).denote
          { diagram_well_formed := batchWellFormed
            boundary_is_root_scoped := by
              intro wire member
              change ((AnchoredWireContractSoundness.moveEndpointsRaw input.val
                drop keep (AnchoredWireContractSoundness.movedEndpoints input
                  redundant drop)).wires wire).scope = input.val.root
              rw [AnchoredWireContractSoundness.moveEndpointsRaw_wire_scope]
              exact sourceRoot wire member }
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) args := by
    by_cases sameSite : (input.val.wires drop).scope = redundantRegion
    · by_cases rootAvailable :
          anchoredContractRootAvailable input survivor keep = true
      · by_cases dropMember : drop ∈ boundary
        · exact AnchoredWireContractSoundness.anchoredContract_sameSite_coalesced_denote_iff
              input redundant survivor
              redundantRegion survivorRegion redundantTerm survivorTerm drop keep
              redundantShape survivorShape redundantOccurs survivorOccurs distinct
              sameDepth rootAvailable certificateEqual sameSite boundary sourceRoot
              dropMember rawMapped rawTransport rawRoot compactedWellFormed
              batchWellFormed Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions)
              (args ∘ Fin.cast (by
                exact (anchoredWireContractInterfaceTransport input redundant
                  survivor drop keep).transportBoundary_length rawTransport))
        · exact AnchoredWireContractSoundness.anchoredContract_sameSite_hidden_denote_iff
              input redundant survivor
              redundantRegion redundantTerm drop keep redundantShape
              redundantOccurs distinct sameSite boundary sourceRoot dropMember
              rawMapped rawTransport rawRoot compactedWellFormed batchWellFormed
              Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions)
              (args ∘ Fin.cast (by
                exact (anchoredWireContractInterfaceTransport input redundant
                  survivor drop keep).transportBoundary_length rawTransport))
      · have unavailable :
            anchoredContractRootAvailable input survivor keep = false := by
          cases h : anchoredContractRootAvailable input survivor keep <;> simp_all
        have dropAbsent := AnchoredWireContractSoundness.anchoredWireContract_hidden_boundary_excludes_drop
          input redundant
            survivor drop keep boundary sourceRoot unavailable rawMapped rawTransport
        exact AnchoredWireContractSoundness.anchoredContract_sameSite_hidden_denote_iff
            input redundant survivor
            redundantRegion redundantTerm drop keep redundantShape redundantOccurs
            distinct sameSite boundary sourceRoot dropAbsent rawMapped rawTransport
            rawRoot compactedWellFormed batchWellFormed Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions)
            (args ∘ Fin.cast (by
              exact (anchoredWireContractInterfaceTransport input redundant
                survivor drop keep).transportBoundary_length rawTransport))
    · have regionNeScope :
          redundantRegion ≠ (input.val.wires drop).scope := Ne.symm sameSite
      have sourceEncloses : input.val.Encloses (input.val.wires drop).scope
          redundantRegion := by
        have encloses := input.property.wire_scopes_enclose drop
          { node := redundant, port := Diagram.CPort.output } redundantOccurs
        simpa [redundantShape] using encloses
      have rawEncloses :
          (anchoredWireContractRaw input redundant drop keep).Encloses
            (input.val.wires drop).scope redundantRegion := by
        obtain ⟨steps, climbed⟩ := sourceEncloses
        refine ⟨steps, ?_⟩
        have rawClimb : ∀ fuel (region : Fin input.val.regionCount),
            (anchoredWireContractRaw input redundant drop keep).climb fuel region =
              input.val.climb fuel region := by
          intro fuel
          induction fuel with
          | zero => intro region; rfl
          | succ fuel ih =>
              intro region
              simp only [Diagram.ConcreteDiagram.climb]
              rw [show (anchoredWireContractRaw input redundant drop keep).regions
                region = input.val.regions region by rfl]
              cases input.val.regions region <;> simp only [ih] <;> rfl
        rw [rawClimb]
        exact climbed
      obtain ⟨nodePath, ⟨nodeRoute⟩⟩ :=
        Diagram.Splice.regionRoute_complete_of_encloses
          (anchoredWireContractRaw input redundant drop keep)
          (input.val.wires drop).scope redundantRegion rawEncloses
      obtain ⟨nodeDepth, nodeRouteDepth⟩ :=
        nodeRoute.hasCutDepth_exists compactedWellFormed
      have rawDepth : ∀ region : Fin input.val.regionCount,
          concreteCutDepth (anchoredWireContractRaw input redundant drop keep)
              region = concreteCutDepth input.val region := by
        intro region
        have aux : ∀ fuel (current : Fin input.val.regionCount),
            concreteCutDepthAux
                (anchoredWireContractRaw input redundant drop keep) fuel current =
              concreteCutDepthAux input.val fuel current := by
          intro fuel
          induction fuel with
          | zero => intro current; rfl
          | succ fuel ih =>
              intro current
              simp only [concreteCutDepthAux]
              rw [show (anchoredWireContractRaw input redundant drop keep).regions
                current = input.val.regions current by rfl]
              cases input.val.regions current <;> simp only [ih]
        unfold concreteCutDepth
        exact aux _ region
      have rawSameDepth :
          concreteCutDepth (anchoredWireContractRaw input redundant drop keep)
              (input.val.wires drop).scope =
            concreteCutDepth (anchoredWireContractRaw input redundant drop keep)
              redundantRegion := by
        rw [rawDepth, rawDepth]
        exact sameDepth
      let compactedChecked : Diagram.CheckedDiagram signature :=
        ⟨anchoredWireContractRaw input redundant drop keep,
          compactedWellFormed⟩
      have nodeDepthZero : nodeDepth = 0 :=
        CongruenceSoundness.route_cutDepth_zero_of_equal compactedChecked
          nodeRoute nodeDepth nodeRouteDepth rawSameDepth
      obtain ⟨rootPath, ⟨rootRoute⟩⟩ :=
        Diagram.Splice.regionRoute_complete_of_encloses
          (anchoredWireContractRaw input redundant drop keep)
          (anchoredWireContractRaw input redundant drop keep).root
          (input.val.wires drop).scope
          (compactedWellFormed.all_regions_reach_root
            (input.val.wires drop).scope)
      by_cases rootAvailable :
          anchoredContractRootAvailable input survivor keep = true
      · by_cases dropMember : drop ∈ boundary
        · exact AnchoredWireContractSoundness.anchoredContract_routed_coalesced_denote_iff
              input redundant survivor
              redundantRegion survivorRegion redundantTerm survivorTerm drop keep
              redundantShape survivorShape redundantOccurs survivorOccurs distinct
              sameDepth rootAvailable certificateEqual regionNeScope boundary
              sourceRoot dropMember rawMapped rawTransport rawRoot
              compactedWellFormed batchWellFormed rawEncloses nodeRoute
              nodeRouteDepth nodeDepthZero rootRoute Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions)
              (args ∘ Fin.cast (by
                exact (anchoredWireContractInterfaceTransport input redundant
                  survivor drop keep).transportBoundary_length rawTransport))
        · exact AnchoredWireContractSoundness.anchoredContract_routed_hidden_denote_iff
              input redundant survivor
              redundantRegion redundantTerm drop keep redundantShape
              redundantOccurs distinct regionNeScope boundary sourceRoot dropMember
              rawMapped rawTransport rawRoot compactedWellFormed batchWellFormed
              rawEncloses nodeRoute nodeRouteDepth nodeDepthZero rootRoute
              Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions)
              (args ∘ Fin.cast (by
                exact (anchoredWireContractInterfaceTransport input redundant
                  survivor drop keep).transportBoundary_length rawTransport))
      · have unavailable :
            anchoredContractRootAvailable input survivor keep = false := by
          cases h : anchoredContractRootAvailable input survivor keep <;> simp_all
        have dropAbsent := AnchoredWireContractSoundness.anchoredWireContract_hidden_boundary_excludes_drop
          input redundant
            survivor drop keep boundary sourceRoot unavailable rawMapped rawTransport
        exact AnchoredWireContractSoundness.anchoredContract_routed_hidden_denote_iff
            input redundant survivor
            redundantRegion redundantTerm drop keep redundantShape redundantOccurs
            distinct regionNeScope boundary sourceRoot dropAbsent rawMapped
            rawTransport rawRoot compactedWellFormed batchWellFormed rawEncloses
            nodeRoute nodeRouteDepth nodeDepthZero rootRoute Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions)
            (args ∘ Fin.cast (by
              exact (anchoredWireContractInterfaceTransport input redundant
                survivor drop keep).transportBoundary_length rawTransport))
  dsimp only
  unfold DirectedEntailment
  change _ ↔ _
  have sourceBatch' :
      (OpenProofState.denote {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      } Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) args) ↔
      (AnchoredWireContractSoundness.anchoredContractBatchOpen input redundant
        drop keep boundary).denote
        { diagram_well_formed := batchWellFormed
          boundary_is_root_scoped := by
            intro wire member
            change ((AnchoredWireContractSoundness.moveEndpointsRaw input.val
              drop keep (AnchoredWireContractSoundness.movedEndpoints input
                redundant drop)).wires wire).scope = input.val.root
            rw [AnchoredWireContractSoundness.moveEndpointsRaw_wire_scope]
            exact sourceRoot wire member }
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) args := by
    simpa [AnchoredWireContractSoundness.endpointMoveSourceCheckedOpen,
      AnchoredWireContractSoundness.endpointMoveSourceOpen,
      AnchoredWireContractSoundness.endpointBatchTargetCheckedOpen,
      AnchoredWireContractSoundness.endpointBatchTargetOpen,
      AnchoredWireContractSoundness.anchoredContractBatchOpen] using sourceBatch
  apply sourceBatch'.trans
  exact compactedBatch.symm

/-- Every successful head-strip receipt is semantically equivalent. -/
theorem applyHeadStrip_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (first second : Fin input.val.nodeCount)
    (payload : HeadStripPayload input first second)
    (receipt : StepReceipt input)
    (happly : applyHeadStrip input payload = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.headStrip first second payload) receipt := by
  have realizes := applyHeadStrip_realizes happly
  have targetWellFormed : (headStripRaw input payload).WellFormed signature :=
    realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      HeadStripSoundness.targetCheckedOpen input payload boundary sourceRoot
        targetWellFormed)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      realizes.operationalIso_to_rawResultOpen htransport
        (boundary.map (Fin.castAdd payload.argumentIndices.length))
        (HeadStripSoundness.expectedTransport input payload boundary sourceRoot))
  intro boundary sourceRoot mapped htransport valid args
  let source := HeadStripSoundness.sourceCheckedOpen input boundary sourceRoot
  let target := HeadStripSoundness.targetCheckedOpen input payload boundary
    sourceRoot targetWellFormed
  let model := Lambda.canonicalModel
  let named := Theory.interpretDefinitions context.definitions
  let simulation := HeadStripSoundness.semanticSimulation input payload
    targetWellFormed named
  let targetArgs := args ∘ Fin.cast
    (HeadStripSoundness.boundaryLengthEq input payload boundary)
  have forwardAllowed : simulation.Allowed .forward input.val.root := by
    trivial
  have backwardAllowed : simulation.Allowed .backward input.val.root := by
    trivial
  have forwardSemantic :=
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source target model named simulation .forward
      (HeadStripSoundness.rootContext input payload boundary sourceRoot
        targetWellFormed named .forward)
      forwardAllowed args targetArgs
      (HeadStripSoundness.boundaryWitness input payload boundary sourceRoot
        targetWellFormed .forward model named args)
  have backwardSemantic :=
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source target model named simulation .backward
      (HeadStripSoundness.rootContext input payload boundary sourceRoot
        targetWellFormed named .backward)
      backwardAllowed args targetArgs
      (HeadStripSoundness.boundaryWitness input payload boundary sourceRoot
        targetWellFormed .backward model named args)
  dsimp only
  unfold DirectedEntailment
  simp only [Step.tag, StepTag.semanticMode]
  cases orientation with
  | forward =>
      intro sourceDenotes
      have targetDenotes := forwardSemantic sourceDenotes
      simpa [source, target, targetArgs, model, named,
        HeadStripSoundness.sourceCheckedOpen,
        HeadStripSoundness.targetCheckedOpen] using targetDenotes
  | backward =>
      intro targetDenotes
      apply backwardSemantic
      simpa [source, target, targetArgs, model, named,
        HeadStripSoundness.sourceCheckedOpen,
        HeadStripSoundness.targetCheckedOpen] using targetDenotes

/-- Every successful fusion receipt is semantically equivalent. -/
theorem applyFusion_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (receipt : StepReceipt input)
    (happly : applyFusion input wire = .ok receipt) :
    SuccessfulReceiptSound context orientation input (.fusion wire)
      receipt := by
  sorry

/-- Every successful fission receipt is semantically equivalent. -/
theorem applyFission_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (path : List Lambda.PathSegment)
    (receipt : StepReceipt input)
    (happly : applyFission input node path = .ok receipt) :
    SuccessfulReceiptSound context orientation input (.fission node path)
      receipt := by
  sorry

end VisualProof.Rule
