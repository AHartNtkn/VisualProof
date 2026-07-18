import VisualProof.Rule.Equational
import VisualProof.Diagram.Concrete.Elaboration.Simulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace HeadStripSoundness

private theorem allFin_succ_last (n : Nat) :
    allFin (n + 1) = (allFin n).map (Fin.castAdd 1) ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]
  apply congrArg (fun xs : List (Fin (n + 1)) => xs ++ [Fin.last n])
  apply List.map_congr_left
  intro index _
  apply Fin.ext
  rfl

private theorem allFin_add (n m : Nat) :
    allFin (n + m) =
      (allFin n).map (Fin.castAdd m) ++
        (allFin m).map (Fin.natAdd n) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, allFin, List.map_nil, List.append_nil]
      have hfun : (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id := by
        funext index
        apply Fin.ext
        rfl
      rw [hfun, List.map_id]
  | succ m ih =>
      change allFin ((n + m) + 1) = _
      rw [allFin_succ_last (n + m), ih, List.map_append,
        allFin_succ_last m, List.map_append, List.map_map,
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

@[simp] theorem headStripRaw_root
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    (headStripRaw input payload).root = input.val.root := rfl

@[simp] theorem headStripRaw_oldWire_scope
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) :
    ((headStripRaw input payload).wires
      (Fin.castAdd payload.argumentIndices.length wire)).scope =
        (input.val.wires wire).scope := by
  simp [headStripRaw]

@[simp] theorem headStripRaw_oldNode
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (node : Fin input.val.nodeCount) :
    (headStripRaw input payload).nodes
        (Fin.castAdd (payload.argumentIndices.length +
          payload.argumentIndices.length) node) =
      input.val.nodes node := by
  simp [headStripRaw]

theorem headStripRaw_oldEndpointOccurs_forward
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount)
    (node : Fin input.val.nodeCount) (port : CPort)
    (occurs : input.val.EndpointOccurs wire { node := node, port := port }) :
    (headStripRaw input payload).EndpointOccurs
      (Fin.castAdd payload.argumentIndices.length wire)
      { node := Fin.castAdd (payload.argumentIndices.length +
          payload.argumentIndices.length) node,
        port := port } := by
  unfold ConcreteDiagram.EndpointOccurs at occurs ⊢
  simp only [headStripRaw, Fin.addCases_left]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨{ node := node, port := port }, occurs, by
    simp [headStripLiftEndpoint]⟩

theorem headStripRaw_addedFreeEndpoint_node_fresh_first
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) (endpoint)
    (member : endpoint ∈ payload.firstAddedFreeEndpoints wire) :
    input.val.nodeCount ≤ endpoint.node.val := by
  simp only [HeadStripPayload.firstAddedFreeEndpoints, List.mem_flatMap,
    List.mem_filterMap] at member
  obtain ⟨position, _, port, _, found⟩ := member
  split at found <;> try contradiction
  cases found
  simp [HeadStripPayload.firstAddedNode]

theorem headStripRaw_addedFreeEndpoint_node_fresh_second
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) (endpoint)
    (member : endpoint ∈ payload.secondAddedFreeEndpoints wire) :
    input.val.nodeCount ≤ endpoint.node.val := by
  simp only [HeadStripPayload.secondAddedFreeEndpoints, List.mem_flatMap,
    List.mem_filterMap] at member
  obtain ⟨position, _, port, _, found⟩ := member
  split at found <;> try contradiction
  cases found
  simp [HeadStripPayload.secondAddedNode]

theorem headStripRaw_oldEndpointOccurs_backward
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWire : Fin (headStripRaw input payload).wireCount)
    (node : Fin input.val.nodeCount) (port : CPort)
    (occurs : (headStripRaw input payload).EndpointOccurs targetWire
      { node := Fin.castAdd (payload.argumentIndices.length +
          payload.argumentIndices.length) node,
        port := port }) :
    ∃ wire,
      Fin.castAdd payload.argumentIndices.length wire = targetWire ∧
        input.val.EndpointOccurs wire { node := node, port := port } := by
  refine Fin.addCases (motive := fun targetWire =>
      (headStripRaw input payload).EndpointOccurs targetWire
        { node := Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length) node, port := port } →
      ∃ wire,
        Fin.castAdd payload.argumentIndices.length wire = targetWire ∧
          input.val.EndpointOccurs wire { node := node, port := port })
    (fun wire occurrence => ?_)
    (fun position occurrence => ?_) targetWire occurs
  · unfold ConcreteDiagram.EndpointOccurs at occurrence ⊢
    simp only [headStripRaw, Fin.addCases_left] at occurrence
    rcases List.mem_append.mp occurrence with oldOrFirst | secondAdded
    rcases List.mem_append.mp oldOrFirst with old | firstAdded
    · obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp old
      rcases original with ⟨originalNode, originalPort⟩
      have nodeEq : originalNode = node := by
        apply Fin.ext
        have equalityNode := congrArg (fun endpoint => endpoint.node.val) equality
        simpa [headStripLiftEndpoint] using equalityNode
      subst originalNode
      have portEq : originalPort = port := by
        exact congrArg CEndpoint.port equality
      subst originalPort
      exact ⟨wire, rfl, originalMember⟩
    · have fresh := headStripRaw_addedFreeEndpoint_node_fresh_first
        payload wire _ firstAdded
      change input.val.nodeCount ≤ node.val at fresh
      omega
    · have fresh := headStripRaw_addedFreeEndpoint_node_fresh_second
        payload wire _ secondAdded
      change input.val.nodeCount ≤ node.val at fresh
      omega
  · unfold ConcreteDiagram.EndpointOccurs at occurrence
    simp only [headStripRaw, Fin.addCases_right] at occurrence
    change (⟨Fin.castAdd
        (payload.argumentIndices.length + payload.argumentIndices.length) node,
          port⟩ : CEndpoint (headStripRaw input payload).nodeCount) ∈
      [⟨payload.firstAddedNode position, .output⟩,
       ⟨payload.secondAddedNode position, .output⟩] at occurrence
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at occurrence
    rcases occurrence with equality | equality
    · have impossible := congrArg (fun endpoint => endpoint.node.val) equality
      simp [HeadStripPayload.firstAddedNode] at impossible
      omega
    · have impossible := congrArg (fun endpoint => endpoint.node.val) equality
      simp [HeadStripPayload.secondAddedNode] at impossible
      omega

theorem headStripRaw_exactScopeWires
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) :
    ConcreteElaboration.exactScopeWires (headStripRaw input payload) region =
      (ConcreteElaboration.exactScopeWires input.val region).map
          (Fin.castAdd payload.argumentIndices.length) ++
        if region = payload.region then
          (allFin payload.argumentIndices.length).map
            (Fin.natAdd input.val.wireCount)
        else [] := by
  unfold ConcreteElaboration.exactScopeWires filterFin
  change List.filter _ (allFin
    (input.val.wireCount + payload.argumentIndices.length)) = _
  rw [allFin_add, List.filter_append]
  simp only [List.filter_map]
  congr 1
  · apply congrArg (List.map (Fin.castAdd payload.argumentIndices.length))
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.val.wireCount))
    funext wire
    simp only [Function.comp_apply]
    rw [headStripRaw_oldWire_scope]
    rfl
  · split <;> rename_i hregion
    · subst region
      apply congrArg (List.map (Fin.natAdd input.val.wireCount))
      apply List.filter_eq_self.mpr
      intro wire _
      simp [headStripRaw]
    · change List.map (Fin.natAdd input.val.wireCount)
          (List.filter _ (allFin payload.argumentIndices.length)) = []
      apply (List.map_eq_nil_iff).mpr
      apply List.filter_eq_nil_iff.mpr
      intro wire _ equality
      have decided : decide
          (((headStripRaw input payload).wires
            (Fin.natAdd input.val.wireCount wire)).scope = region) = true :=
        equality
      simp only [decide_eq_true_eq, headStripRaw, Fin.addCases_right] at decided
      exact hregion decided.symm

def liftOccurrence
    (payload : HeadStripPayload input first second)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount) :
    ConcreteElaboration.LocalOccurrence (headStripRaw input payload).regionCount
      (headStripRaw input payload).nodeCount :=
  match occurrence with
  | .node node => .node (Fin.castAdd
      (payload.argumentIndices.length + payload.argumentIndices.length) node)
  | .child child => .child child

theorem headStripRaw_regular_localOccurrences
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region) :
    ConcreteElaboration.localOccurrences (headStripRaw input payload) region =
      (ConcreteElaboration.localOccurrences input.val region).map
        (liftOccurrence payload) := by
  unfold ConcreteElaboration.localOccurrences filterFin
  change
    (List.filter _ (allFin (input.val.nodeCount +
      (payload.argumentIndices.length +
        payload.argumentIndices.length)))).map
          (@ConcreteElaboration.LocalOccurrence.node input.val.regionCount
            (input.val.nodeCount + (payload.argumentIndices.length +
              payload.argumentIndices.length))) ++
      (List.filter _ (allFin input.val.regionCount)).map
          (@ConcreteElaboration.LocalOccurrence.child input.val.regionCount
            (input.val.nodeCount + (payload.argumentIndices.length +
              payload.argumentIndices.length))) = _
  rw [allFin_add input.val.nodeCount
    (payload.argumentIndices.length + payload.argumentIndices.length),
    List.filter_append]
  simp only [List.filter_map, List.map_append, List.map_map]
  have freshFalse : ∀ node : Fin (payload.argumentIndices.length +
      payload.argumentIndices.length),
      ((headStripRaw input payload).nodes
        (Fin.natAdd input.val.nodeCount node)).region ≠ region := by
    intro node
    refine Fin.addCases (motive := fun node =>
        ((headStripRaw input payload).nodes
          (Fin.natAdd input.val.nodeCount node)).region ≠ region)
      (fun position equality => ?_) (fun position equality => ?_) node
    · apply regular
      simpa only [headStripRaw, Fin.addCases_right, Fin.addCases_left,
        CNode.region] using equality.symm
    · apply regular
      simpa only [headStripRaw, Fin.addCases_right, CNode.region] using
        equality.symm
  have freshEmpty :
      List.filter
        ((fun node => decide (((headStripRaw input payload).nodes node).region =
          region)) ∘ Fin.natAdd input.val.nodeCount)
        (allFin (payload.argumentIndices.length +
          payload.argumentIndices.length)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro node _ member
    exact freshFalse node (of_decide_eq_true member)
  have oldFilter :
      List.filter
        ((fun node => decide (((headStripRaw input payload).nodes node).region =
          region)) ∘ Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length))
        (allFin input.val.nodeCount) =
      List.filter (fun node => decide ((input.val.nodes node).region = region))
        (allFin input.val.nodeCount) := by
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.val.nodeCount))
    funext node
    simp only [Function.comp_apply, headStripRaw_oldNode]
    rfl
  dsimp only [headStripRaw] at freshEmpty oldFilter ⊢
  rw [freshEmpty, oldFilter]
  simp only [List.map_nil, List.append_nil, List.map_map]
  congr 1

def sourceNodeOccurrences (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount) :
    List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount) :=
  (filterFin fun node => decide ((input.val.nodes node).region = region)).map
    ConcreteElaboration.LocalOccurrence.node

def sourceChildOccurrences (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount) :
    List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount) :=
  (filterFin fun child =>
    decide ((input.val.regions child).parent? = some region)).map
      ConcreteElaboration.LocalOccurrence.child

def firstAddedOccurrences
    (payload : HeadStripPayload input first second) :
    List (ConcreteElaboration.LocalOccurrence
      (headStripRaw input payload).regionCount
      (headStripRaw input payload).nodeCount) :=
  (allFin payload.argumentIndices.length).map fun position =>
    .node (payload.firstAddedNode position)

def secondAddedOccurrences
    (payload : HeadStripPayload input first second) :
    List (ConcreteElaboration.LocalOccurrence
      (headStripRaw input payload).regionCount
      (headStripRaw input payload).nodeCount) :=
  (allFin payload.argumentIndices.length).map fun position =>
    .node (payload.secondAddedNode position)

theorem source_localOccurrences
    (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount) :
    ConcreteElaboration.localOccurrences input.val region =
      sourceNodeOccurrences input region ++ sourceChildOccurrences input region :=
  rfl

theorem headStripRaw_focused_localOccurrences
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    ConcreteElaboration.localOccurrences (headStripRaw input payload)
        payload.region =
      (sourceNodeOccurrences input payload.region).map
          (liftOccurrence payload) ++
        firstAddedOccurrences payload ++ secondAddedOccurrences payload ++
        (sourceChildOccurrences input payload.region).map
          (liftOccurrence payload) := by
  unfold ConcreteElaboration.localOccurrences filterFin
    sourceNodeOccurrences sourceChildOccurrences
    firstAddedOccurrences secondAddedOccurrences
  change
    (List.filter _ (allFin (input.val.nodeCount +
      (payload.argumentIndices.length +
        payload.argumentIndices.length)))).map
          (@ConcreteElaboration.LocalOccurrence.node input.val.regionCount
            (input.val.nodeCount + (payload.argumentIndices.length +
              payload.argumentIndices.length))) ++
      (List.filter _ (allFin input.val.regionCount)).map
          (@ConcreteElaboration.LocalOccurrence.child input.val.regionCount
            (input.val.nodeCount + (payload.argumentIndices.length +
              payload.argumentIndices.length))) = _
  rw [allFin_add input.val.nodeCount
    (payload.argumentIndices.length + payload.argumentIndices.length),
    List.filter_append]
  simp only [List.filter_map, List.map_append, List.map_map]
  rw [allFin_add payload.argumentIndices.length
    payload.argumentIndices.length, List.filter_append]
  simp only [List.filter_map, List.map_append, List.map_map]
  have oldFilter :
      List.filter
        ((fun node => decide (((headStripRaw input payload).nodes node).region =
          payload.region)) ∘ Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length))
        (allFin input.val.nodeCount) =
      filterFin fun node =>
        decide ((input.val.nodes node).region = payload.region) := by
    unfold filterFin
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.val.nodeCount))
    funext node
    simp only [Function.comp_apply, headStripRaw_oldNode]
    rfl
  have firstFilter :
      List.filter
        (((fun node => decide (((headStripRaw input payload).nodes node).region =
          payload.region)) ∘ Fin.natAdd input.val.nodeCount) ∘
            Fin.castAdd payload.argumentIndices.length)
        (allFin payload.argumentIndices.length) =
      allFin payload.argumentIndices.length := by
    apply List.filter_eq_self.mpr
    intro position member
    simp only [Function.comp_apply, headStripRaw, Fin.addCases_right,
      Fin.addCases_left, CNode.region, decide_true]
  have secondFilter :
      List.filter
        (((fun node => decide (((headStripRaw input payload).nodes node).region =
          payload.region)) ∘ Fin.natAdd input.val.nodeCount) ∘
            Fin.natAdd payload.argumentIndices.length)
        (allFin payload.argumentIndices.length) =
      allFin payload.argumentIndices.length := by
    apply List.filter_eq_self.mpr
    intro position member
    simp only [Function.comp_apply, headStripRaw, Fin.addCases_right,
      CNode.region, decide_true]
  have childFilter :
      List.filter
        (fun child => decide (((headStripRaw input payload).regions child).parent? =
          some payload.region)) (allFin input.val.regionCount) =
    filterFin fun child =>
        decide ((input.val.regions child).parent? = some payload.region) := by
    rfl
  dsimp only [headStripRaw] at oldFilter firstFilter secondFilter childFilter ⊢
  rw [oldFilter, firstFilter, secondFilter]
  unfold filterFin
  have oldMap :
      List.map (ConcreteElaboration.LocalOccurrence.node ∘
          Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length))
          (List.filter
            (fun node => decide ((input.val.nodes node).region = payload.region))
            (allFin input.val.nodeCount)) =
      List.map (liftOccurrence payload ∘
          ConcreteElaboration.LocalOccurrence.node)
          (List.filter
            (fun node => decide ((input.val.nodes node).region = payload.region))
            (allFin input.val.nodeCount)) := by
    congr 1
  have firstMap :
      List.map
          (((@ConcreteElaboration.LocalOccurrence.node input.val.regionCount
            (input.val.nodeCount + (payload.argumentIndices.length +
              payload.argumentIndices.length))) ∘
            Fin.natAdd input.val.nodeCount) ∘
              Fin.castAdd payload.argumentIndices.length)
          (allFin payload.argumentIndices.length) =
      List.map (fun position =>
          (@ConcreteElaboration.LocalOccurrence.node input.val.regionCount
            (input.val.nodeCount + (payload.argumentIndices.length +
              payload.argumentIndices.length)))
            (payload.firstAddedNode position))
          (allFin payload.argumentIndices.length) := by
    apply List.map_congr_left
    intro position member
    rfl
  have secondMap :
      List.map
          (((@ConcreteElaboration.LocalOccurrence.node input.val.regionCount
            (input.val.nodeCount + (payload.argumentIndices.length +
              payload.argumentIndices.length))) ∘
            Fin.natAdd input.val.nodeCount) ∘
              Fin.natAdd payload.argumentIndices.length)
          (allFin payload.argumentIndices.length) =
      List.map (fun position =>
          (@ConcreteElaboration.LocalOccurrence.node input.val.regionCount
            (input.val.nodeCount + (payload.argumentIndices.length +
              payload.argumentIndices.length)))
            (payload.secondAddedNode position))
          (allFin payload.argumentIndices.length) := by
    apply List.map_congr_left
    intro position member
    rfl
  have childMap :
      List.map (@ConcreteElaboration.LocalOccurrence.child input.val.regionCount
          (input.val.nodeCount + (payload.argumentIndices.length +
            payload.argumentIndices.length)))
          (List.filter
            (fun child => decide
              ((input.val.regions child).parent? = some payload.region))
            (allFin input.val.regionCount)) =
      List.map (liftOccurrence payload ∘
          (@ConcreteElaboration.LocalOccurrence.child input.val.regionCount
            input.val.nodeCount))
          (List.filter
            (fun child => decide
              ((input.val.regions child).parent? = some payload.region))
            (allFin input.val.regionCount)) := by
    congr 1
  let oldTarget := List.map
    ((@ConcreteElaboration.LocalOccurrence.node
      (headStripRaw input payload).regionCount
      (headStripRaw input payload).nodeCount) ∘
      Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length))
    (List.filter (fun node =>
      decide ((input.val.nodes node).region = payload.region))
      (allFin input.val.nodeCount))
  let oldSource := List.map
    (liftOccurrence payload ∘
      (@ConcreteElaboration.LocalOccurrence.node input.val.regionCount
        input.val.nodeCount))
    (List.filter (fun node =>
      decide ((input.val.nodes node).region = payload.region))
      (allFin input.val.nodeCount))
  let firstTarget := List.map
    (((@ConcreteElaboration.LocalOccurrence.node
      (headStripRaw input payload).regionCount
      (headStripRaw input payload).nodeCount) ∘ Fin.natAdd input.val.nodeCount) ∘
      Fin.castAdd payload.argumentIndices.length)
    (allFin payload.argumentIndices.length)
  let firstSource := List.map (fun position =>
      (@ConcreteElaboration.LocalOccurrence.node
        (headStripRaw input payload).regionCount
        (headStripRaw input payload).nodeCount)
        (payload.firstAddedNode position))
    (allFin payload.argumentIndices.length)
  let secondTarget := List.map
    (((@ConcreteElaboration.LocalOccurrence.node
      (headStripRaw input payload).regionCount
      (headStripRaw input payload).nodeCount) ∘ Fin.natAdd input.val.nodeCount) ∘
      Fin.natAdd payload.argumentIndices.length)
    (allFin payload.argumentIndices.length)
  let secondSource := List.map (fun position =>
      (@ConcreteElaboration.LocalOccurrence.node
        (headStripRaw input payload).regionCount
        (headStripRaw input payload).nodeCount)
        (payload.secondAddedNode position))
    (allFin payload.argumentIndices.length)
  let childTarget := List.map
    (@ConcreteElaboration.LocalOccurrence.child
      (headStripRaw input payload).regionCount
      (headStripRaw input payload).nodeCount)
    (List.filter (fun child => decide
      ((input.val.regions child).parent? = some payload.region))
      (allFin input.val.regionCount))
  let childSource := List.map
    (liftOccurrence payload ∘
      (@ConcreteElaboration.LocalOccurrence.child input.val.regionCount
        input.val.nodeCount))
    (List.filter (fun child => decide
      ((input.val.regions child).parent? = some payload.region))
      (allFin input.val.regionCount))
  have oldEq : oldTarget = oldSource := oldMap
  have firstEq : firstTarget = firstSource := firstMap
  have secondEq : secondTarget = secondSource := secondMap
  have childEq : childTarget = childSource := childMap
  change (oldTarget ++ (firstTarget ++ secondTarget)) ++ childTarget =
    ((oldSource ++ firstSource) ++ secondSource) ++ childSource
  rw [oldEq, firstEq, secondEq, childEq]
  exact congrArg (fun items => items ++ childSource)
    (List.append_assoc oldSource firstSource secondSource).symm

structure ContextEmbedding
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext (headStripRaw input payload)) where
  index : Fin source.length → Fin target.length
  get : ∀ i, target.get (index i) =
    Fin.castAdd payload.argumentIndices.length (source.get i)
  mem_old : ∀ wire : Fin input.val.wireCount,
    Fin.castAdd payload.argumentIndices.length wire ∈ target ↔ wire ∈ source

namespace ContextEmbedding

noncomputable def ofMem
    {input : CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    {payload : HeadStripPayload input first second}
    {source : ConcreteElaboration.WireContext input.val}
    {target : ConcreteElaboration.WireContext (headStripRaw input payload)}
    (hmem : ∀ wire : Fin input.val.wireCount,
      Fin.castAdd payload.argumentIndices.length wire ∈ target ↔
        wire ∈ source) :
    ContextEmbedding input payload source target where
  index := fun i => Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete
      ((hmem (source.get i)).mpr (List.get_mem source i)))
  get := by
    intro i
    exact ConcreteElaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (ConcreteElaboration.WireContext.lookup?_complete
          ((hmem (source.get i)).mpr (List.get_mem source i))))
  mem_old := hmem

noncomputable def extend
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount) :
    ContextEmbedding input payload (source.extend region)
      (target.extend region) :=
  ofMem (by
    intro wire
    unfold ConcreteElaboration.WireContext.extend
    constructor
    · intro member
      rcases List.mem_append.mp member with inherited | localScope
      · exact List.mem_append_left _ ((embedding.mem_old wire).mp inherited)
      · apply List.mem_append_right
        apply (ConcreteElaboration.mem_exactScopeWires input.val region wire).mpr
        have scope := (ConcreteElaboration.mem_exactScopeWires
          (headStripRaw input payload) region
          (Fin.castAdd payload.argumentIndices.length wire)).mp localScope
        simpa using scope
    · intro member
      rcases List.mem_append.mp member with inherited | localScope
      · exact List.mem_append_left _ ((embedding.mem_old wire).mpr inherited)
      · apply List.mem_append_right
        apply (ConcreteElaboration.mem_exactScopeWires
          (headStripRaw input payload) region
          (Fin.castAdd payload.argumentIndices.length wire)).mpr
        have scope := (ConcreteElaboration.mem_exactScopeWires input.val region
          wire).mp localScope
        simpa using scope)

end ContextEmbedding

theorem compileNode_old
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripRaw input payload).WellFormed signature)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext (headStripRaw input payload))
    (embedding : ContextEmbedding input payload source target)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (headStripRaw input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (headStripRaw input payload) sourceBinders targetBinders)
    (targetNodup : target.Nodup)
    (node : Fin input.val.nodeCount) :
    ConcreteElaboration.compileNode? signature (headStripRaw input payload)
        target targetBinders
        (Fin.castAdd (payload.argumentIndices.length +
          payload.argumentIndices.length) node) =
      (ConcreteElaboration.compileNode? signature input.val source sourceBinders
        node).map (fun item =>
          (item.renameWires embedding.index).renameRelations
            (ConcreteElaboration.IdentityBinderWitness.relationMap
              binderWitness)) := by
  apply ConcreteElaboration.compileNode?_map source target sourceBinders
    targetBinders node
    (Fin.castAdd (payload.argumentIndices.length +
      payload.argumentIndices.length) node)
    id id embedding.index
    (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
  · rw [headStripRaw_oldNode]
    cases input.val.nodes node <;> rfl
  · intro port
    apply ConcreteElaboration.resolvePort?_map_of_occurrence source target node
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) node)
      (Fin.castAdd payload.argumentIndices.length) embedding.index targetNodup
      embedding.get embedding.mem_old
    · intro wire candidatePort occurs
      exact headStripRaw_oldEndpointOccurs_forward input payload wire node
        candidatePort occurs
    · intro targetWire candidatePort occurs
      exact headStripRaw_oldEndpointOccurs_backward input payload targetWire node
        candidatePort occurs
    · exact targetWellFormed.wire_endpoints_are_disjoint
  · intro region binder nodeShape
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simp [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming]

def sourceOpen (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := input.val
  boundary := boundary

def targetOpen (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := headStripRaw input payload
  boundary := boundary.map (Fin.castAdd payload.argumentIndices.length)

theorem expectedTransport
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    (headStripInterfaceTransport input payload).transportBoundary boundary =
      some (boundary.map (Fin.castAdd payload.argumentIndices.length)) := by
  apply InterfaceTransport.transportBoundary_eq_map
  intro wire member
  unfold headStripInterfaceTransport InterfaceTransport.append
    InterfaceTransport.rootFiltered
  dsimp only
  have castEq :
      Fin.cast (show input.val.wireCount + payload.argumentIndices.length =
        (headStripRaw input payload).wireCount by rfl)
          (Fin.castAdd payload.argumentIndices.length wire) =
        Fin.castAdd payload.argumentIndices.length wire := by
    apply Fin.ext
    rfl
  rw [castEq]
  change (if ((headStripRaw input payload).wires
      (Fin.castAdd payload.argumentIndices.length wire)).scope =
        (headStripRaw input payload).root then
      some (Fin.castAdd payload.argumentIndices.length wire) else none) =
    some (Fin.castAdd payload.argumentIndices.length wire)
  rw [headStripRaw_oldWire_scope]
  simp [sourceRoot wire member]

def targetCheckedOpen
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed : (headStripRaw input payload).WellFormed signature) :
    CheckedOpenDiagram signature :=
  ⟨targetOpen input payload boundary, {
    diagram_well_formed := targetWellFormed
    boundary_is_root_scoped := by
      intro mapped member
      obtain ⟨wire, wireMember, rfl⟩ := List.mem_map.mp member
      exact headStripRaw_oldWire_scope input payload wire |>.trans
        (sourceRoot wire wireMember) }⟩

end HeadStripSoundness

end VisualProof.Rule
