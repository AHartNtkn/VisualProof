import VisualProof.Rule.Soundness.Equational.HeadStripSimulation
import VisualProof.Rule.Soundness.Comprehension.InstantiationFilteredCompiler

namespace VisualProof.Rule

open VisualProof
open Lambda
open VisualProof.Data.Finite
open Diagram
open Theory

namespace HeadStripCompaction

abbrev Expanded (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :=
  headStripExpandedRaw input payload

abbrev Reduced (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :=
  headStripRaw input payload

/-- Embed every surviving reduced wire into the append-only proof diagram. -/
def expandWire (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Fin (Reduced input payload).wireCount → Fin (Expanded input payload).wireCount :=
  fun wire => Fin.addCases
    (fun old => Fin.castAdd payload.argumentIndices.length
      ((headStripWireDomain input.val payload.outputWire).origin old))
    (fun fresh => Fin.natAdd input.val.wireCount fresh)
    wire

/-- Embed every surviving reduced node into the append-only proof diagram. -/
def expandNode (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Fin (Reduced input payload).nodeCount → Fin (Expanded input payload).nodeCount :=
  fun node => Fin.addCases
    (fun old => Fin.castAdd
      (payload.argumentIndices.length + payload.argumentIndices.length)
      ((headStripNodeDomain input.val first second).origin old))
    (fun fresh => Fin.natAdd input.val.nodeCount fresh)
    node

theorem expandWire_injective (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Function.Injective (expandWire input payload) := by
  intro left right equality
  refine Fin.addCases (motive := fun left =>
      expandWire input payload left = expandWire input payload right →
        left = right) (fun left equality => ?_)
    (fun left equality => ?_) left equality
  · refine Fin.addCases (motive := fun right =>
        expandWire input payload (Fin.castAdd payload.argumentIndices.length left) =
            expandWire input payload right →
          Fin.castAdd payload.argumentIndices.length left = right)
      (fun right equality => ?_) (fun right equality => ?_) right equality
    · have origins :
          (headStripWireDomain input.val payload.outputWire).origin left =
            (headStripWireDomain input.val payload.outputWire).origin right := by
        apply Fin.ext
        simpa [expandWire] using congrArg Fin.val equality
      have indices :=
        (headStripWireDomain input.val payload.outputWire).origin_injective origins
      subst right
      rfl
    · have values := congrArg Fin.val equality
      simp [expandWire] at values
      omega
  · refine Fin.addCases (motive := fun right =>
        expandWire input payload (Fin.natAdd
            (headStripWireDomain input.val payload.outputWire).count left) =
            expandWire input payload right →
          Fin.natAdd (headStripWireDomain input.val payload.outputWire).count
            left = right)
      (fun right equality => ?_) (fun right equality => ?_) right equality
    · have values := congrArg Fin.val equality
      simp [expandWire] at values
      omega
    · apply Fin.ext
      simpa [expandWire] using congrArg Fin.val equality

theorem expandNode_injective (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Function.Injective (expandNode input payload) := by
  intro left right equality
  refine Fin.addCases (motive := fun left =>
      expandNode input payload left = expandNode input payload right →
        left = right) (fun left equality => ?_)
    (fun left equality => ?_) left equality
  · refine Fin.addCases (motive := fun right =>
        expandNode input payload (Fin.castAdd
            (payload.argumentIndices.length + payload.argumentIndices.length)
            left) = expandNode input payload right →
          Fin.castAdd
            (payload.argumentIndices.length + payload.argumentIndices.length)
            left = right)
      (fun right equality => ?_) (fun right equality => ?_) right equality
    · have origins :
          (headStripNodeDomain input.val first second).origin left =
            (headStripNodeDomain input.val first second).origin right := by
        apply Fin.ext
        simpa [expandNode] using congrArg Fin.val equality
      have indices :=
        (headStripNodeDomain input.val first second).origin_injective origins
      subst right
      rfl
    · have values := congrArg Fin.val equality
      simp [expandNode] at values
      omega
  · refine Fin.addCases (motive := fun right =>
        expandNode input payload (Fin.natAdd
            (headStripNodeDomain input.val first second).count left) =
            expandNode input payload right →
          Fin.natAdd (headStripNodeDomain input.val first second).count left =
            right)
      (fun right equality => ?_) (fun right equality => ?_) right equality
    · have values := congrArg Fin.val equality
      simp [expandNode] at values
      omega
    · apply Fin.ext
      simpa [expandNode] using congrArg Fin.val equality

@[simp] theorem expandWire_scope (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin (Reduced input payload).wireCount) :
    ((Expanded input payload).wires (expandWire input payload wire)).scope =
      ((Reduced input payload).wires wire).scope := by
  refine Fin.addCases (motive := fun wire =>
      ((Expanded input payload).wires (expandWire input payload wire)).scope =
        ((Reduced input payload).wires wire).scope)
    (fun old => ?_) (fun fresh => ?_) wire
  · simp [Expanded, Reduced, expandWire, headStripExpandedRaw, headStripRaw]
  · simp [Expanded, Reduced, expandWire, headStripExpandedRaw, headStripRaw]

@[simp] theorem expandNode_value (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (node : Fin (Reduced input payload).nodeCount) :
    (Expanded input payload).nodes (expandNode input payload node) =
      (Reduced input payload).nodes node := by
  refine Fin.addCases (motive := fun node =>
      (Expanded input payload).nodes (expandNode input payload node) =
        (Reduced input payload).nodes node)
    (fun old => ?_) (fun fresh => ?_) node
  · simp [Expanded, Reduced, expandNode, headStripExpandedRaw, headStripRaw]
  · refine Fin.addCases (fun firstFresh => ?_) (fun secondFresh => ?_) fresh
    · simp [Expanded, Reduced, expandNode, headStripExpandedRaw, headStripRaw]
    · simp [Expanded, Reduced, expandNode, headStripExpandedRaw, headStripRaw]

def expandEndpoint (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (endpoint : CEndpoint (Reduced input payload).nodeCount) :
    CEndpoint (Expanded input payload).nodeCount :=
  { node := expandNode input payload endpoint.node, port := endpoint.port }

@[simp] theorem expandNode_firstReduced (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    expandNode input payload (payload.firstReducedNode position) =
      payload.firstAddedNode position := by
  simp [expandNode, HeadStripPayload.firstReducedNode,
    HeadStripPayload.firstAddedNode]

@[simp] theorem expandNode_secondReduced (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    expandNode input payload (payload.secondReducedNode position) =
      payload.secondAddedNode position := by
  simp [expandNode, HeadStripPayload.secondReducedNode,
    HeadStripPayload.secondAddedNode]

theorem expandEndpoint_injective (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Function.Injective (expandEndpoint input payload) := by
  rintro ⟨leftNode, leftPort⟩ ⟨rightNode, rightPort⟩ equality
  have nodes := congrArg CEndpoint.node equality
  have ports := congrArg CEndpoint.port equality
  simp only [expandEndpoint] at nodes ports
  have nodeEq := expandNode_injective input payload nodes
  cases nodeEq
  cases ports
  rfl

private theorem mem_map_expandEndpoint_iff
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (endpoint : CEndpoint (Reduced input payload).nodeCount)
    (endpoints : List (CEndpoint (Reduced input payload).nodeCount)) :
    expandEndpoint input payload endpoint ∈
        endpoints.map (expandEndpoint input payload) ↔
      endpoint ∈ endpoints := by
  constructor
  · intro member
    obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
    have originalEq := expandEndpoint_injective input payload equality
    simpa [originalEq] using originalMember
  · intro member
    exact List.mem_map.mpr ⟨endpoint, member, rfl⟩

private theorem mem_reindexed_endpoint_iff
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (oldNode : Fin (headStripNodeDomain input.val first second).count)
    (port : CPort)
    (endpoints : List (CEndpoint input.val.nodeCount)) :
    ({ node := oldNode, port := port } :
        CEndpoint (headStripNodeDomain input.val first second).count) ∈
        endpoints.filterMap
          (headStripEndpoint? (headStripNodeDomain input.val first second)) ↔
      ({ node := (headStripNodeDomain input.val first second).origin oldNode,
          port := port } : CEndpoint input.val.nodeCount) ∈ endpoints := by
  constructor
  · intro member
    obtain ⟨original, originalMember, mapped⟩ := List.mem_filterMap.mp member
    rcases original with ⟨originalNode, originalPort⟩
    unfold headStripEndpoint? at mapped
    cases indexed : (headStripNodeDomain input.val first second).index?
        originalNode with
    | none => simp [indexed] at mapped
    | some compact =>
        simp only [indexed, Option.map_some, Option.some.injEq] at mapped
        have compactEq : compact = oldNode := by
          exact congrArg CEndpoint.node mapped
        subst compact
        have originalEq :=
          (headStripNodeDomain input.val first second).index?_eq_some_iff
            originalNode oldNode |>.mp indexed
        have portEq : originalPort = port := congrArg CEndpoint.port mapped
        subst originalNode
        subst originalPort
        exact originalMember
  · intro member
    apply List.mem_filterMap.mpr
    let original : CEndpoint input.val.nodeCount :=
      { node := (headStripNodeDomain input.val first second).origin oldNode
        port := port }
    refine ⟨original, ?_, ?_⟩
    · exact member
    · unfold headStripEndpoint?
      rw [(headStripNodeDomain input.val first second).index?_origin oldNode]
      rfl

private theorem firstReducedFreeEndpoints_mem_iff
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount)
    (endpoint : CEndpoint (Reduced input payload).nodeCount) :
    expandEndpoint input payload endpoint ∈
        payload.firstAddedFreeEndpoints wire ↔
      endpoint ∈ payload.firstReducedFreeEndpoints wire := by
  unfold HeadStripPayload.firstAddedFreeEndpoints
    HeadStripPayload.firstReducedFreeEndpoints
  constructor
  · intro member
    obtain ⟨position, positionMember, innerMember⟩ := List.mem_flatMap.mp member
    obtain ⟨port, portMember, found⟩ := List.mem_filterMap.mp innerMember
    apply List.mem_flatMap.mpr
    refine ⟨position, positionMember, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨port, portMember, ?_⟩
    by_cases hwire : payload.firstWire
        ((payload.firstArgument
          (payload.argumentIndices.get position)).freeSupport.get port) = wire
    · rw [if_pos hwire] at found ⊢
      have expanded : expandEndpoint input payload
          { node := payload.firstReducedNode position, port := .free port } =
          { node := payload.firstAddedNode position, port := .free port } := by
        exact congrArg (fun node => ({ node := node, port := .free port } :
          CEndpoint (Expanded input payload).nodeCount))
            (expandNode_firstReduced input payload position)
      have mapped := expanded.trans (Option.some.inj found)
      exact congrArg some
        (expandEndpoint_injective input payload mapped)
    · rw [if_neg hwire] at found
      contradiction
  · intro member
    obtain ⟨position, positionMember, innerMember⟩ := List.mem_flatMap.mp member
    obtain ⟨port, portMember, found⟩ := List.mem_filterMap.mp innerMember
    apply List.mem_flatMap.mpr
    refine ⟨position, positionMember, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨port, portMember, ?_⟩
    by_cases hwire : payload.firstWire
        ((payload.firstArgument
          (payload.argumentIndices.get position)).freeSupport.get port) = wire
    · rw [if_pos hwire] at found ⊢
      have expanded : expandEndpoint input payload
          { node := payload.firstReducedNode position, port := .free port } =
          { node := payload.firstAddedNode position, port := .free port } := by
        exact congrArg (fun node => ({ node := node, port := .free port } :
          CEndpoint (Expanded input payload).nodeCount))
            (expandNode_firstReduced input payload position)
      exact congrArg some (expanded.symm.trans
        (congrArg (expandEndpoint input payload) (Option.some.inj found)))
    · rw [if_neg hwire] at found
      contradiction

private theorem secondReducedFreeEndpoints_mem_iff
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount)
    (endpoint : CEndpoint (Reduced input payload).nodeCount) :
    expandEndpoint input payload endpoint ∈
        payload.secondAddedFreeEndpoints wire ↔
      endpoint ∈ payload.secondReducedFreeEndpoints wire := by
  unfold HeadStripPayload.secondAddedFreeEndpoints
    HeadStripPayload.secondReducedFreeEndpoints
  constructor
  · intro member
    obtain ⟨position, positionMember, innerMember⟩ := List.mem_flatMap.mp member
    obtain ⟨port, portMember, found⟩ := List.mem_filterMap.mp innerMember
    apply List.mem_flatMap.mpr
    refine ⟨position, positionMember, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨port, portMember, ?_⟩
    by_cases hwire : payload.secondWire
        ((payload.secondArgument
          (payload.argumentIndices.get position)).freeSupport.get port) = wire
    · rw [if_pos hwire] at found ⊢
      have expanded : expandEndpoint input payload
          { node := payload.secondReducedNode position, port := .free port } =
          { node := payload.secondAddedNode position, port := .free port } := by
        exact congrArg (fun node => ({ node := node, port := .free port } :
          CEndpoint (Expanded input payload).nodeCount))
            (expandNode_secondReduced input payload position)
      have mapped := expanded.trans (Option.some.inj found)
      exact congrArg some
        (expandEndpoint_injective input payload mapped)
    · rw [if_neg hwire] at found
      contradiction
  · intro member
    obtain ⟨position, positionMember, innerMember⟩ := List.mem_flatMap.mp member
    obtain ⟨port, portMember, found⟩ := List.mem_filterMap.mp innerMember
    apply List.mem_flatMap.mpr
    refine ⟨position, positionMember, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨port, portMember, ?_⟩
    by_cases hwire : payload.secondWire
        ((payload.secondArgument
          (payload.argumentIndices.get position)).freeSupport.get port) = wire
    · rw [if_pos hwire] at found ⊢
      have expanded : expandEndpoint input payload
          { node := payload.secondReducedNode position, port := .free port } =
          { node := payload.secondAddedNode position, port := .free port } := by
        exact congrArg (fun node => ({ node := node, port := .free port } :
          CEndpoint (Expanded input payload).nodeCount))
            (expandNode_secondReduced input payload position)
      exact congrArg some (expanded.symm.trans
        (congrArg (expandEndpoint input payload) (Option.some.inj found)))
    · rw [if_neg hwire] at found
      contradiction

private theorem firstReducedFreeEndpoint_fresh
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) (endpoint)
    (member : endpoint ∈ payload.firstReducedFreeEndpoints wire) :
    (headStripNodeDomain input.val first second).count ≤ endpoint.node.val := by
  simp only [HeadStripPayload.firstReducedFreeEndpoints, List.mem_flatMap,
    List.mem_filterMap] at member
  obtain ⟨position, _, port, _, found⟩ := member
  split at found <;> try contradiction
  cases found
  simp [HeadStripPayload.firstReducedNode]

private theorem secondReducedFreeEndpoint_fresh
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) (endpoint)
    (member : endpoint ∈ payload.secondReducedFreeEndpoints wire) :
    (headStripNodeDomain input.val first second).count ≤ endpoint.node.val := by
  simp only [HeadStripPayload.secondReducedFreeEndpoints, List.mem_flatMap,
    List.mem_filterMap] at member
  obtain ⟨position, _, port, _, found⟩ := member
  split at found <;> try contradiction
  cases found
  simp [HeadStripPayload.secondReducedNode]

private theorem headStripLiftEndpoint_injective (added : Nat) :
    Function.Injective (@headStripLiftEndpoint nodes added) := by
  rintro ⟨leftNode, leftPort⟩ ⟨rightNode, rightPort⟩ equality
  have nodes := congrArg CEndpoint.node equality
  have ports := congrArg CEndpoint.port equality
  simp only [headStripLiftEndpoint] at nodes ports
  have nodeEq : leftNode = rightNode := by
    apply Fin.ext
    simpa using congrArg Fin.val nodes
  cases nodeEq
  cases ports
  rfl

@[simp] theorem expandWire_fresh (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    expandWire input payload
        (Fin.natAdd (headStripWireDomain input.val payload.outputWire).count
          position) =
      Fin.natAdd input.val.wireCount position := by
  simp [expandWire]

theorem expandEndpoint_occurs (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin (Reduced input payload).wireCount)
    (endpoint : CEndpoint (Reduced input payload).nodeCount) :
    (Reduced input payload).EndpointOccurs wire endpoint ↔
      (Expanded input payload).EndpointOccurs (expandWire input payload wire)
        (expandEndpoint input payload endpoint) := by
  refine Fin.addCases (motive := fun wire =>
      (Reduced input payload).EndpointOccurs wire endpoint ↔
        (Expanded input payload).EndpointOccurs (expandWire input payload wire)
          (expandEndpoint input payload endpoint))
    (fun old => ?_) (fun fresh => ?_) wire
  · rcases endpoint with ⟨node, port⟩
    refine Fin.addCases (motive := fun node =>
        (Reduced input payload).EndpointOccurs
            (Fin.castAdd payload.argumentIndices.length old) { node, port } ↔
          (Expanded input payload).EndpointOccurs
            (expandWire input payload
              (Fin.castAdd payload.argumentIndices.length old))
            (expandEndpoint input payload { node, port }))
      (fun oldNode => ?_) (fun freshNode => ?_) node
    · simp only [ConcreteDiagram.EndpointOccurs, Reduced, Expanded, headStripRaw,
        headStripExpandedRaw, expandWire, expandEndpoint, expandNode,
        Fin.addCases_left]
      let originalEndpoint : CEndpoint input.val.nodeCount :=
        { node := (headStripNodeDomain input.val first second).origin oldNode
          port := port }
      have rawIff :
          ({ node := Fin.castAdd
              (payload.argumentIndices.length + payload.argumentIndices.length)
              oldNode, port := port } : CEndpoint (Reduced input payload).nodeCount) ∈
              (List.map (headStripLiftEndpoint
                  (payload.argumentIndices.length + payload.argumentIndices.length))
                  (List.filterMap
                    (headStripEndpoint?
                      (headStripNodeDomain input.val first second))
                    (input.val.wires ((headStripWireDomain input.val
                      payload.outputWire).origin old)).endpoints) ++
                payload.firstReducedFreeEndpoints
                  ((headStripWireDomain input.val payload.outputWire).origin old)) ++
              payload.secondReducedFreeEndpoints
                ((headStripWireDomain input.val payload.outputWire).origin old) ↔
            originalEndpoint ∈
              (input.val.wires ((headStripWireDomain input.val
                payload.outputWire).origin old)).endpoints := by
        constructor
        · intro member
          rcases List.mem_append.mp member with oldOrFirst | secondFree
          · rcases List.mem_append.mp oldOrFirst with oldMapped | firstFree
            · obtain ⟨compactEndpoint, compactMember, equality⟩ :=
                List.mem_map.mp oldMapped
              have compactEq : compactEndpoint =
                  ({ node := oldNode, port := port } : CEndpoint
                    (headStripNodeDomain input.val first second).count) :=
                headStripLiftEndpoint_injective _ equality
              subst compactEndpoint
              exact (mem_reindexed_endpoint_iff input oldNode port _).mp
                compactMember
            · have fresh := firstReducedFreeEndpoint_fresh payload _ _ firstFree
              change (headStripNodeDomain input.val first second).count ≤
                oldNode.val at fresh
              omega
          · have fresh := secondReducedFreeEndpoint_fresh payload _ _ secondFree
            change (headStripNodeDomain input.val first second).count ≤
              oldNode.val at fresh
            omega
        · intro member
          apply List.mem_append_left
          apply List.mem_append_left
          apply List.mem_map.mpr
          refine ⟨{ node := oldNode, port := port }, ?_, rfl⟩
          exact (mem_reindexed_endpoint_iff input oldNode port _).mpr member
      have expandedIff :
          ({ node := Fin.castAdd
              (payload.argumentIndices.length + payload.argumentIndices.length)
              ((headStripNodeDomain input.val first second).origin oldNode),
              port := port } : CEndpoint (Expanded input payload).nodeCount) ∈
              List.map (headStripLiftEndpoint
                  (payload.argumentIndices.length + payload.argumentIndices.length))
                  (input.val.wires ((headStripWireDomain input.val
                    payload.outputWire).origin old)).endpoints ++
                (payload.firstAddedFreeEndpoints
                    ((headStripWireDomain input.val payload.outputWire).origin old) ++
                  payload.secondAddedFreeEndpoints
                    ((headStripWireDomain input.val payload.outputWire).origin old)) ↔
            originalEndpoint ∈
              (input.val.wires ((headStripWireDomain input.val
                payload.outputWire).origin old)).endpoints := by
        constructor
        · intro member
          rcases List.mem_append.mp member with oldMapped | added
          · obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp oldMapped
            have originalEq : original = originalEndpoint :=
              headStripLiftEndpoint_injective _ equality
            simpa [originalEq] using originalMember
          · rcases List.mem_append.mp added with firstFree | secondFree
            · have fresh :=
                HeadStripSoundness.headStripExpandedRaw_addedFreeEndpoint_node_fresh_first
                  payload _ _ firstFree
              change input.val.nodeCount ≤
                ((headStripNodeDomain input.val first second).origin oldNode).val
                at fresh
              omega
            · have fresh :=
                HeadStripSoundness.headStripExpandedRaw_addedFreeEndpoint_node_fresh_second
                  payload _ _ secondFree
              change input.val.nodeCount ≤
                ((headStripNodeDomain input.val first second).origin oldNode).val
                at fresh
              omega
        · intro member
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨originalEndpoint, member, rfl⟩
      simpa only [List.append_assoc] using rawIff.trans expandedIff.symm
    · simp only [ConcreteDiagram.EndpointOccurs, Reduced, Expanded, headStripRaw,
        headStripExpandedRaw, expandWire, expandEndpoint, expandNode,
        Fin.addCases_left, Fin.addCases_right]
      let current : CEndpoint (Reduced input payload).nodeCount :=
        { node := Fin.natAdd
            (headStripNodeDomain input.val first second).count freshNode
          port := port }
      have rawOldImpossible : current ∉
          List.map (headStripLiftEndpoint
            (payload.argumentIndices.length + payload.argumentIndices.length))
            (List.filterMap
              (headStripEndpoint? (headStripNodeDomain input.val first second))
              (input.val.wires ((headStripWireDomain input.val
                payload.outputWire).origin old)).endpoints) := by
        intro member
        obtain ⟨compact, _, equality⟩ := List.mem_map.mp member
        have values := congrArg (fun endpoint => endpoint.node.val) equality
        simp [current, headStripLiftEndpoint] at values
        omega
      have expandedOldImpossible : expandEndpoint input payload current ∉
          List.map (headStripLiftEndpoint
            (payload.argumentIndices.length + payload.argumentIndices.length))
            (input.val.wires ((headStripWireDomain input.val
              payload.outputWire).origin old)).endpoints := by
        intro member
        obtain ⟨original, _, equality⟩ := List.mem_map.mp member
        have values := congrArg (fun endpoint => endpoint.node.val) equality
        simp [current, expandEndpoint, expandNode, headStripLiftEndpoint]
          at values
        omega
      have correspondence :
          current ∈
              (List.map (headStripLiftEndpoint
                  (payload.argumentIndices.length + payload.argumentIndices.length))
                  (List.filterMap
                    (headStripEndpoint?
                      (headStripNodeDomain input.val first second))
                    (input.val.wires ((headStripWireDomain input.val
                      payload.outputWire).origin old)).endpoints) ++
                payload.firstReducedFreeEndpoints
                  ((headStripWireDomain input.val payload.outputWire).origin old)) ++
              payload.secondReducedFreeEndpoints
                ((headStripWireDomain input.val payload.outputWire).origin old) ↔
            expandEndpoint input payload current ∈
              (List.map (headStripLiftEndpoint
                  (payload.argumentIndices.length + payload.argumentIndices.length))
                  (input.val.wires ((headStripWireDomain input.val
                    payload.outputWire).origin old)).endpoints ++
                payload.firstAddedFreeEndpoints
                  ((headStripWireDomain input.val payload.outputWire).origin old)) ++
              payload.secondAddedFreeEndpoints
                ((headStripWireDomain input.val payload.outputWire).origin old) := by
        constructor
        · intro member
          rcases List.mem_append.mp member with oldOrFirst | secondMember
          · rcases List.mem_append.mp oldOrFirst with oldMember | firstMember
            · exact False.elim (rawOldImpossible oldMember)
            · apply List.mem_append_left
              apply List.mem_append_right
              exact (firstReducedFreeEndpoints_mem_iff input payload _ current).mpr
                firstMember
          · apply List.mem_append_right
            exact (secondReducedFreeEndpoints_mem_iff input payload _ current).mpr
              secondMember
        · intro member
          rcases List.mem_append.mp member with oldOrFirst | secondMember
          · rcases List.mem_append.mp oldOrFirst with oldMember | firstMember
            · exact False.elim (expandedOldImpossible oldMember)
            · apply List.mem_append_left
              apply List.mem_append_right
              exact (firstReducedFreeEndpoints_mem_iff input payload _ current).mp
                firstMember
          · apply List.mem_append_right
            exact (secondReducedFreeEndpoints_mem_iff input payload _ current).mp
              secondMember
      simpa [current, expandEndpoint, expandNode] using correspondence
  · unfold ConcreteDiagram.EndpointOccurs
    have endpointList :
        ((Expanded input payload).wires
            (expandWire input payload
              (Fin.natAdd
                (headStripWireDomain input.val payload.outputWire).count fresh))).endpoints =
          ((((Reduced input payload).wires
            (Fin.natAdd
              (headStripWireDomain input.val payload.outputWire).count fresh)).endpoints).map
            (expandEndpoint input payload)) := by
      simp [Expanded, Reduced, expandWire, expandEndpoint, expandNode,
        headStripExpandedRaw, headStripRaw,
        HeadStripPayload.firstReducedNode, HeadStripPayload.firstAddedNode,
        HeadStripPayload.secondReducedNode, HeadStripPayload.secondAddedNode]
    change endpoint ∈ ((Reduced input payload).wires
        (Fin.natAdd
          (headStripWireDomain input.val payload.outputWire).count fresh)).endpoints ↔
      expandEndpoint input payload endpoint ∈
        ((Expanded input payload).wires
          (expandWire input payload
            (Fin.natAdd
              (headStripWireDomain input.val payload.outputWire).count fresh))).endpoints
    rw [endpointList]
    exact (mem_map_expandEndpoint_iff input payload endpoint _).symm

/-- A reduced lexical context embeds into the proof-only expanded context.
The sole expanded wire outside the image is the discharged output wire. -/
structure ContextEmbedding
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (source : ConcreteElaboration.WireContext (Expanded input payload))
    (target : ConcreteElaboration.WireContext (Reduced input payload)) where
  index : Fin target.length → Fin source.length
  get : ∀ i, source.get (index i) =
    expandWire input payload (target.get i)
  mem : ∀ wire : Fin (Reduced input payload).wireCount,
    expandWire input payload wire ∈ source ↔ wire ∈ target

namespace ContextEmbedding

noncomputable def ofMem
    {input : CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    {payload : HeadStripPayload input first second}
    {source : ConcreteElaboration.WireContext (Expanded input payload)}
    {target : ConcreteElaboration.WireContext (Reduced input payload)}
    (hmem : ∀ wire : Fin (Reduced input payload).wireCount,
      expandWire input payload wire ∈ source ↔ wire ∈ target) :
    ContextEmbedding input payload source target where
  index := fun i => Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete
      ((hmem (target.get i)).mpr (List.get_mem target i)))
  get := by
    intro i
    exact ConcreteElaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (ConcreteElaboration.WireContext.lookup?_complete
          ((hmem (target.get i)).mpr (List.get_mem target i))))
  mem := hmem

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
      · exact List.mem_append_left _ ((embedding.mem wire).mp inherited)
      · apply List.mem_append_right
        apply (ConcreteElaboration.mem_exactScopeWires
          (Reduced input payload) region wire).mpr
        have scope := (ConcreteElaboration.mem_exactScopeWires
          (Expanded input payload) region (expandWire input payload wire)).mp
            localScope
        simpa using scope
    · intro member
      rcases List.mem_append.mp member with inherited | localScope
      · exact List.mem_append_left _ ((embedding.mem wire).mpr inherited)
      · apply List.mem_append_right
        apply (ConcreteElaboration.mem_exactScopeWires
          (Expanded input payload) region
          (expandWire input payload wire)).mpr
        have scope := (ConcreteElaboration.mem_exactScopeWires
          (Reduced input payload) region wire).mp localScope
        simpa using scope)

theorem index_injective
    (embedding : ContextEmbedding input payload source target)
    (targetNodup : target.Nodup) : Function.Injective embedding.index := by
  intro left right equality
  have mappedGet := congrArg source.get equality
  have wireGet : target.get left = target.get right := by
    apply expandWire_injective input payload
    exact (embedding.get left).symm.trans
      (mappedGet.trans (embedding.get right))
  apply Fin.ext
  exact (List.getElem_inj (i := left.val) (j := right.val)
    (h₀ := left.isLt) (h₁ := right.isLt) targetNodup).mp (by
      simpa only [List.get_eq_getElem] using wireGet)

end ContextEmbedding

theorem expandWire_not_output (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin (Reduced input payload).wireCount) :
    expandWire input payload wire ≠
      Fin.castAdd payload.argumentIndices.length payload.outputWire := by
  refine Fin.addCases (motive := fun wire =>
      expandWire input payload wire ≠
        Fin.castAdd payload.argumentIndices.length payload.outputWire)
    (fun old equality => ?_) (fun fresh equality => ?_) wire
  · have originalEq :
        (headStripWireDomain input.val payload.outputWire).origin old =
          payload.outputWire := by
      apply Fin.ext
      simpa [expandWire] using congrArg Fin.val equality
    have survives :=
      (headStripWireDomain input.val payload.outputWire).origin_survives old
    have excluded :
        (headStripWireDomain input.val payload.outputWire).origin old ≠
          payload.outputWire := by
      simpa [headStripWireDomain] using survives
    exact excluded originalEq
  · have values := congrArg Fin.val equality
    simp [expandWire] at values
    omega

theorem expandedOccurrence_backward (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWire : Fin (Expanded input payload).wireCount)
    (node : Fin (Reduced input payload).nodeCount) (port : CPort)
    (occurs : (Expanded input payload).EndpointOccurs targetWire
      { node := expandNode input payload node, port := port }) :
    ∃ sourceWire,
      expandWire input payload sourceWire = targetWire ∧
        (Reduced input payload).EndpointOccurs sourceWire { node, port } := by
  refine Fin.addCases (motive := fun targetWire =>
      (Expanded input payload).EndpointOccurs targetWire
          { node := expandNode input payload node, port := port } →
        ∃ sourceWire,
          expandWire input payload sourceWire = targetWire ∧
            (Reduced input payload).EndpointOccurs sourceWire { node, port })
    (fun old occurrence => ?_) (fun fresh occurrence => ?_) targetWire occurs
  · by_cases output : old = payload.outputWire
    · subst old
      unfold ConcreteDiagram.EndpointOccurs at occurrence
      simp only [Expanded, headStripExpandedRaw, Fin.addCases_left] at occurrence
      have firstEmpty : payload.firstAddedFreeEndpoints payload.outputWire = [] := by
        simp [HeadStripPayload.firstAddedFreeEndpoints,
          payload.firstWire_ne_output]
      have secondEmpty : payload.secondAddedFreeEndpoints payload.outputWire = [] := by
        simp [HeadStripPayload.secondAddedFreeEndpoints,
          payload.secondWire_ne_output]
      rw [firstEmpty, secondEmpty] at occurrence
      simp only [List.append_nil] at occurrence
      obtain ⟨original, originalMember, endpointEq⟩ := List.mem_map.mp occurrence
      have originalValueMember : original.node.val ∈
          (input.val.wires payload.outputWire).endpoints.map
            (fun endpoint => endpoint.node.val) :=
        List.mem_map.mpr ⟨original, originalMember, rfl⟩
      have originalValueEither :
          original.node.val = first.val ∨ original.node.val = second.val := by
        rcases payload.outputEndpoints with endpoints | endpoints
        · rw [endpoints] at originalValueMember
          simpa using originalValueMember
        · rw [endpoints] at originalValueMember
          simpa [or_comm] using originalValueMember
      have mappedValueEq :
          (expandNode input payload node).val = original.node.val :=
        by
          simpa [headStripLiftEndpoint] using
            (congrArg (fun endpoint => endpoint.node.val) endpointEq).symm
      have nodeEither :
          expandNode input payload node =
              Fin.castAdd (payload.argumentIndices.length +
                payload.argumentIndices.length) first ∨
            expandNode input payload node =
              Fin.castAdd (payload.argumentIndices.length +
                payload.argumentIndices.length) second := by
        rcases originalValueEither with originalFirst | originalSecond
        · apply Or.inl
          apply Fin.ext
          exact mappedValueEq.trans originalFirst
        · apply Or.inr
          apply Fin.ext
          exact mappedValueEq.trans originalSecond
      rcases nodeEither with nodeEq | nodeEq
      · exfalso
        refine Fin.addCases (motive := fun node =>
            expandNode input payload node = Fin.castAdd
              (payload.argumentIndices.length + payload.argumentIndices.length)
              first → False)
          (fun oldNode equality => ?_) (fun freshNode equality => ?_) node nodeEq
        · have originEq :
              (headStripNodeDomain input.val first second).origin oldNode =
                first := by
            apply Fin.ext
            simpa [expandNode] using congrArg Fin.val equality
          have survives :=
            (headStripNodeDomain input.val first second).origin_survives oldNode
          have excludedPair :
              (headStripNodeDomain input.val first second).origin oldNode ≠ first ∧
                (headStripNodeDomain input.val first second).origin oldNode ≠
                  second := by
            simpa [headStripNodeDomain] using survives
          have excluded :
              (headStripNodeDomain input.val first second).origin oldNode ≠
                first := excludedPair.1
          exact excluded originEq
        · have values := congrArg Fin.val equality
          simp [expandNode] at values
          omega
      · exfalso
        refine Fin.addCases (motive := fun node =>
            expandNode input payload node = Fin.castAdd
              (payload.argumentIndices.length + payload.argumentIndices.length)
              second → False)
          (fun oldNode equality => ?_) (fun freshNode equality => ?_) node nodeEq
        · have originEq :
              (headStripNodeDomain input.val first second).origin oldNode =
                second := by
            apply Fin.ext
            simpa [expandNode] using congrArg Fin.val equality
          have survives :=
            (headStripNodeDomain input.val first second).origin_survives oldNode
          have excludedPair :
              (headStripNodeDomain input.val first second).origin oldNode ≠ first ∧
                (headStripNodeDomain input.val first second).origin oldNode ≠
                  second := by
            simpa [headStripNodeDomain] using survives
          have excluded :
              (headStripNodeDomain input.val first second).origin oldNode ≠
                second := excludedPair.2
          exact excluded originEq
        · have values := congrArg Fin.val equality
          simp [expandNode] at values
          omega
    · have survives :
          (headStripWireDomain input.val payload.outputWire).survives old = true := by
        simp [headStripWireDomain, output]
      let compact :=
        (headStripWireDomain input.val payload.outputWire).index old survives
      have compactOrigin :
          (headStripWireDomain input.val payload.outputWire).origin compact = old := by
        exact (headStripWireDomain input.val payload.outputWire).origin_index
          old survives
      refine ⟨Fin.castAdd payload.argumentIndices.length compact, ?_, ?_⟩
      · apply Fin.ext
        simp only [expandWire, Fin.addCases_left]
        change ((headStripWireDomain input.val payload.outputWire).origin compact).val =
          old.val
        rw [compactOrigin]
      · apply (expandEndpoint_occurs input payload
          (Fin.castAdd payload.argumentIndices.length compact) { node, port }).mpr
        have wireEq : expandWire input payload
            (Fin.castAdd payload.argumentIndices.length compact) =
              Fin.castAdd payload.argumentIndices.length old := by
          apply Fin.ext
          simp only [expandWire, Fin.addCases_left]
          change ((headStripWireDomain input.val payload.outputWire).origin compact).val =
            old.val
          rw [compactOrigin]
        rw [wireEq]
        exact occurrence
  · refine ⟨Fin.natAdd
        (headStripWireDomain input.val payload.outputWire).count fresh, ?_, ?_⟩
    · simp [expandWire]
    · apply (expandEndpoint_occurs input payload
        (Fin.natAdd
          (headStripWireDomain input.val payload.outputWire).count fresh)
        { node, port }).mpr
      simpa [expandWire] using occurrence

theorem resolvePort_map
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (source : ConcreteElaboration.WireContext (Expanded input payload))
    (target : ConcreteElaboration.WireContext (Reduced input payload))
    (embedding : ContextEmbedding input payload source target)
    (sourceNodup : source.Nodup)
    (targetNode : Fin (Reduced input payload).nodeCount)
    (port : CPort) :
    ConcreteElaboration.resolvePort? (Expanded input payload) source
        (expandNode input payload targetNode) port =
      (ConcreteElaboration.resolvePort? (Reduced input payload) target
        targetNode port).map embedding.index := by
  apply ConcreteElaboration.resolvePort?_map_of_occurrence target source
    targetNode (expandNode input payload targetNode)
    (expandWire input payload) embedding.index sourceNodup embedding.get
    embedding.mem
    (fun wire port occurrence =>
      (expandEndpoint_occurs input payload wire { node := targetNode, port }).mp
        occurrence)
    (fun wire port occurrence =>
      expandedOccurrence_backward input payload wire targetNode port occurrence)
    expandedWellFormed.wire_endpoints_are_disjoint port

def expandOccurrence (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    ConcreteElaboration.LocalOccurrence (Reduced input payload).regionCount
        (Reduced input payload).nodeCount →
      ConcreteElaboration.LocalOccurrence (Expanded input payload).regionCount
        (Expanded input payload).nodeCount
  | .node node => .node (expandNode input payload node)
  | .child child => .child child

theorem compileNode_expand
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (source : ConcreteElaboration.WireContext (Reduced input payload))
    (target : ConcreteElaboration.WireContext (Expanded input payload))
    (embedding : ContextEmbedding input payload target source)
    (targetNodup : target.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext
      (Reduced input payload) sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (Expanded input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness
      (Reduced input payload) (Expanded input payload)
      sourceBinders targetBinders)
    (node : Fin (Reduced input payload).nodeCount) :
    ConcreteElaboration.compileNode? signature (Expanded input payload)
        target targetBinders (expandNode input payload node) =
      (ConcreteElaboration.compileNode? signature (Reduced input payload)
        source sourceBinders node).map fun item =>
          (item.renameWires embedding.index).renameRelations
            (ConcreteElaboration.IdentityBinderWitness.relationMap
              binderWitness) := by
  apply ConcreteElaboration.compileNode?_map source target sourceBinders
    targetBinders node (expandNode input payload node) id id embedding.index
    (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
  · rw [expandNode_value]
    cases (Reduced input payload).nodes node <;> rfl
  · intro port
    exact resolvePort_map input payload expandedWellFormed target source
      embedding targetNodup node port
  · intro region binder nodeShape
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simp [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming]

private theorem length_allFin (n : Nat) : (allFin n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allFin, ih]

private theorem get_allFin (n : Nat) (index : Fin (allFin n).length) :
    (allFin n).get index = Fin.cast (length_allFin n) index := by
  apply Fin.ext
  simp [allFin_eq_finRange, List.get_eq_getElem, List.getElem_finRange]

private theorem allFin_map_origin (domain : SurvivorDomain size) :
    (allFin domain.count).map domain.origin = domain.enumeration := by
  apply List.ext_get
  · simp only [List.length_map]
    rw [length_allFin]
    rfl
  · intro index leftValid rightValid
    simp only [List.length_map] at leftValid
    simp only [List.get_eq_getElem, List.getElem_map]
    change domain.origin ((allFin domain.count).get ⟨index, leftValid⟩) =
      domain.enumeration.get ⟨index, rightValid⟩
    rw [get_allFin]
    apply congrArg domain.origin
    apply Fin.ext
    rfl

private theorem filter_allFin_map_origin (domain : SurvivorDomain size)
    (predicate : Fin size → Bool) :
    ((allFin domain.count).filter (predicate ∘ domain.origin)).map
        domain.origin =
      domain.enumeration.filter predicate := by
  rw [← List.filter_map, allFin_map_origin]

private theorem filter_allFin_map_origin_eq (domain : SurvivorDomain size)
    (predicate : Fin size → Bool) :
    ((allFin domain.count).filter (predicate ∘ domain.origin)).map
        domain.origin =
      (allFin size).filter (fun original =>
        domain.survives original && predicate original) := by
  rw [filter_allFin_map_origin]
  unfold SurvivorDomain.enumeration filterFin
  rw [List.filter_filter]
  apply congrArg (fun accepted => List.filter accepted (allFin size))
  funext original
  exact Bool.and_comm _ _

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
      have allFin_succ_last (k : Nat) :
          allFin (k + 1) = (allFin k).map (Fin.castAdd 1) ++ [Fin.last k] := by
        rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]
        congr 1
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

/-- The occurrences retained by destructive head strip inside the append-only
proof diagram.  The two original term occurrences are the only rejected
occurrences; their private output wire is handled by focused existential
transport. -/
def keepExpandedOccurrence (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    ConcreteElaboration.LocalOccurrence (Expanded input payload).regionCount
      (Expanded input payload).nodeCount → Bool
  | .node node =>
      decide (node ≠ Fin.castAdd
          (payload.argumentIndices.length + payload.argumentIndices.length) first ∧
        node ≠ Fin.castAdd
          (payload.argumentIndices.length + payload.argumentIndices.length) second)
  | .child _ => true

theorem reduced_localOccurrences_map (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) :
    (ConcreteElaboration.localOccurrences (Reduced input payload) region).map
        (expandOccurrence input payload) =
      (ConcreteElaboration.localOccurrences (Expanded input payload) region).filter
        (keepExpandedOccurrence input payload) := by
  unfold ConcreteElaboration.localOccurrences
  rw [List.map_append, List.filter_append]
  congr 1
  · rw [List.map_map, List.filter_map]
    simp only [Reduced, Expanded, headStripRaw, headStripExpandedRaw]
    change
      List.map (fun node => ConcreteElaboration.LocalOccurrence.node
          (expandNode input payload node))
        (List.filter (fun node => decide
          (((Reduced input payload).nodes node).region = region))
          (allFin ((headStripNodeDomain input.val first second).count +
            (payload.argumentIndices.length + payload.argumentIndices.length)))) =
      List.map ConcreteElaboration.LocalOccurrence.node
        (List.filter
          (keepExpandedOccurrence input payload ∘
            ConcreteElaboration.LocalOccurrence.node)
          (List.filter (fun node => decide
            (((Expanded input payload).nodes node).region = region))
            (allFin (input.val.nodeCount +
              (payload.argumentIndices.length + payload.argumentIndices.length)))))
    rw [allFin_add
      (headStripNodeDomain input.val first second).count
      (payload.argumentIndices.length + payload.argumentIndices.length),
      allFin_add input.val.nodeCount
        (payload.argumentIndices.length + payload.argumentIndices.length)]
    have rawSplit :
        List.filter (fun node : Fin (Reduced input payload).nodeCount =>
            decide (((Reduced input payload).nodes node).region = region))
          ((allFin (headStripNodeDomain input.val first second).count).map
              (Fin.castAdd
                (payload.argumentIndices.length + payload.argumentIndices.length)) ++
            (allFin (payload.argumentIndices.length +
              payload.argumentIndices.length)).map
              (Fin.natAdd
                (headStripNodeDomain input.val first second).count)) =
        List.filter (fun node : Fin (Reduced input payload).nodeCount =>
            decide (((Reduced input payload).nodes node).region = region))
            ((allFin (headStripNodeDomain input.val first second).count).map
              (Fin.castAdd
                (payload.argumentIndices.length + payload.argumentIndices.length))) ++
          List.filter (fun node : Fin (Reduced input payload).nodeCount =>
            decide (((Reduced input payload).nodes node).region = region))
            ((allFin (payload.argumentIndices.length +
              payload.argumentIndices.length)).map
              (Fin.natAdd
                (headStripNodeDomain input.val first second).count)) := by
      exact List.filter_append _ _
    rw [rawSplit]
    rw [List.map_append]
    let targetOld : List (Fin (Expanded input payload).nodeCount) :=
      (allFin input.val.nodeCount).map
        (Fin.castAdd
          (payload.argumentIndices.length + payload.argumentIndices.length))
    let targetFresh : List (Fin (Expanded input payload).nodeCount) :=
      (allFin (payload.argumentIndices.length +
        payload.argumentIndices.length)).map (Fin.natAdd input.val.nodeCount)
    change _ = List.map ConcreteElaboration.LocalOccurrence.node
      (List.filter
        (keepExpandedOccurrence input payload ∘
          ConcreteElaboration.LocalOccurrence.node)
        (List.filter (fun node => decide
          (((Expanded input payload).nodes node).region = region))
          (targetOld ++ targetFresh)))
    rw [List.filter_append targetOld targetFresh]
    rw [List.filter_append]
    rw [List.filter_map, List.filter_map, List.map_map, List.map_map]
    simp only [Function.comp_apply, expandNode, Fin.addCases_left,
      Fin.addCases_right]
    rw [List.map_append]
    have castEqIff (left right : Fin input.val.nodeCount) :
        Fin.castAdd
            (payload.argumentIndices.length + payload.argumentIndices.length) left =
          Fin.castAdd
            (payload.argumentIndices.length + payload.argumentIndices.length) right ↔
        left = right := by
      constructor
      · intro equality
        apply Fin.ext
        simpa using congrArg Fin.val equality
      · intro equality
        subst right
        rfl
    have freshNeOld
        (fresh : Fin (payload.argumentIndices.length +
          payload.argumentIndices.length))
        (old : Fin input.val.nodeCount) :
        Fin.natAdd input.val.nodeCount fresh ≠
          Fin.castAdd
            (payload.argumentIndices.length + payload.argumentIndices.length) old := by
      intro equality
      have values := congrArg Fin.val equality
      simp at values
      omega
    congr 1
    · have identifiers := filter_allFin_map_origin_eq
          (headStripNodeDomain input.val first second)
          (fun node => decide ((input.val.nodes node).region = region))
      let liftOld : Fin input.val.nodeCount →
          ConcreteElaboration.LocalOccurrence (Expanded input payload).regionCount
            (Expanded input payload).nodeCount :=
        fun node => .node (Fin.castAdd
          (payload.argumentIndices.length + payload.argumentIndices.length) node)
      have occurrences := congrArg (List.map liftOld) identifiers
      simpa [headStripNodeDomain, keepExpandedOccurrence, targetOld,
        headStripRaw, headStripExpandedRaw, Function.comp_def,
        List.map_map, List.filter_map, liftOld, castEqIff] using occurrences
    · simp [keepExpandedOccurrence, targetFresh, headStripRaw,
        headStripExpandedRaw, Function.comp_def, List.filter_map, List.map_map,
        freshNeOld]
  · rw [List.map_map, List.filter_map]
    change List.map ConcreteElaboration.LocalOccurrence.child
        (filterFin fun child =>
          decide ((input.val.regions child).parent? = some region)) =
      List.map ConcreteElaboration.LocalOccurrence.child
        (List.filter (fun _ => true)
          (filterFin fun child =>
            decide ((input.val.regions child).parent? = some region)))
    rw [List.filter_eq_self.mpr]
    intro occurrence member
    rfl

theorem expandedWire_preimage (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin (Expanded input payload).wireCount)
    (notOutput : wire ≠
      Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    ∃ reduced, expandWire input payload reduced = wire := by
  refine Fin.addCases (m := input.val.wireCount)
    (n := payload.argumentIndices.length)
    (motive := fun wire =>
      wire ≠
          Fin.castAdd payload.argumentIndices.length payload.outputWire →
        ∃ reduced, expandWire input payload reduced = wire)
    (fun old excluded => ?_) (fun fresh excluded => ?_) wire notOutput
  · have oldNe : old ≠ payload.outputWire := by
      intro equality
      exact excluded (congrArg (Fin.castAdd payload.argumentIndices.length) equality)
    have survives :
        (headStripWireDomain input.val payload.outputWire).survives old = true := by
      simp [headStripWireDomain, oldNe]
    let compact :=
      (headStripWireDomain input.val payload.outputWire).index old survives
    refine ⟨Fin.castAdd payload.argumentIndices.length compact, ?_⟩
    apply Fin.ext
    simp only [expandWire, Fin.addCases_left]
    change ((headStripWireDomain input.val payload.outputWire).origin compact).val =
      old.val
    rw [(headStripWireDomain input.val payload.outputWire).origin_index old survives]
  · refine ⟨Fin.natAdd
      (headStripWireDomain input.val payload.outputWire).count fresh, ?_⟩
    simp [expandWire]

noncomputable def localEmbedding (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) :
    ContextEmbedding input payload
      (ConcreteElaboration.exactScopeWires (Expanded input payload) region)
      (ConcreteElaboration.exactScopeWires (Reduced input payload) region) :=
  ContextEmbedding.ofMem (by
    intro wire
    simp only [ConcreteElaboration.mem_exactScopeWires, expandWire_scope]
    rfl)

theorem localEmbedding_surjective_regular (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) region).length) :
    ∃ reducedIndex,
      (localEmbedding input payload region).index reducedIndex = index := by
  let expandedWire :=
    (ConcreteElaboration.exactScopeWires
      (Expanded input payload) region).get index
  have expandedScope :
      ((Expanded input payload).wires expandedWire).scope = region :=
    (ConcreteElaboration.mem_exactScopeWires
      (Expanded input payload) region expandedWire).mp
        (List.get_mem _ index)
  have notOutput : expandedWire ≠
      Fin.castAdd payload.argumentIndices.length payload.outputWire := by
    intro equality
    have scopeEq := congrArg
      (fun wire => ((Expanded input payload).wires wire).scope) equality
    have outputScope :
        ((Expanded input payload).wires
          (Fin.castAdd payload.argumentIndices.length payload.outputWire)).scope =
            payload.region := by
      simpa using payload.noAdditionalExistentialAttachment
    exact regular
      (outputScope.symm.trans (scopeEq.symm.trans expandedScope)).symm
  obtain ⟨reducedWire, expandedEq⟩ :=
    expandedWire_preimage input payload expandedWire notOutput
  have reducedMember : reducedWire ∈
      ConcreteElaboration.exactScopeWires (Reduced input payload) region := by
    apply (ConcreteElaboration.mem_exactScopeWires
      (Reduced input payload) region reducedWire).mpr
    rw [← expandWire_scope input payload reducedWire, expandedEq]
    exact expandedScope
  obtain ⟨reducedIndex, reducedGet⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete reducedMember
  have reducedAt := ConcreteElaboration.WireContext.lookup?_sound reducedGet
  refine ⟨reducedIndex, ?_⟩
  apply Fin.ext
  exact (List.getElem_inj
    (ConcreteElaboration.exactScopeWires_nodup
      (Expanded input payload) region)).mp (by
      simpa only [List.get_eq_getElem] using
        ((localEmbedding input payload region).get reducedIndex).trans
          ((congrArg (expandWire input payload) reducedAt).trans expandedEq))

theorem localEmbedding_preimage_of_not_output (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) region).length)
    (notOutput :
      (ConcreteElaboration.exactScopeWires
        (Expanded input payload) region).get index ≠
        Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    ∃ reducedIndex,
      (localEmbedding input payload region).index reducedIndex = index := by
  let expandedWire :=
    (ConcreteElaboration.exactScopeWires
      (Expanded input payload) region).get index
  have expandedScope :
      ((Expanded input payload).wires expandedWire).scope = region :=
    (ConcreteElaboration.mem_exactScopeWires
      (Expanded input payload) region expandedWire).mp
        (List.get_mem _ index)
  obtain ⟨reducedWire, expandedEq⟩ :=
    expandedWire_preimage input payload expandedWire notOutput
  have reducedMember : reducedWire ∈
      ConcreteElaboration.exactScopeWires (Reduced input payload) region := by
    apply (ConcreteElaboration.mem_exactScopeWires
      (Reduced input payload) region reducedWire).mpr
    rw [← expandWire_scope input payload reducedWire, expandedEq]
    exact expandedScope
  obtain ⟨reducedIndex, reducedGet⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete reducedMember
  have reducedAt := ConcreteElaboration.WireContext.lookup?_sound reducedGet
  refine ⟨reducedIndex, ?_⟩
  apply Fin.ext
  exact (List.getElem_inj
    (ConcreteElaboration.exactScopeWires_nodup
      (Expanded input payload) region)).mp (by
      simpa only [List.get_eq_getElem] using
        ((localEmbedding input payload region).get reducedIndex).trans
          ((congrArg (expandWire input payload) reducedAt).trans expandedEq))

theorem extend_index_outer
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (source : ConcreteElaboration.WireContext (Expanded input payload))
    (target : ConcreteElaboration.WireContext (Reduced input payload))
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount)
    (expandedNodup : (source.extend region).Nodup)
    (index : Fin target.length) :
    (embedding.extend region).index
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              (Reduced input payload) region).length index)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend source region).symm
        (Fin.castAdd
          (ConcreteElaboration.exactScopeWires
            (Expanded input payload) region).length
          (embedding.index index)) := by
  let leftIndex := (embedding.extend region).index
    (Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires
          (Reduced input payload) region).length index))
  let rightIndex := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source region).symm
    (Fin.castAdd
      (ConcreteElaboration.exactScopeWires
        (Expanded input payload) region).length
      (embedding.index index))
  have extendedGet := (embedding.extend region).get
    (Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires
          (Reduced input payload) region).length index))
  have extendedGet' :
      (source.extend region).get leftIndex =
        expandWire input payload (target.get index) := by
    simpa [leftIndex, ConcreteElaboration.WireContext.extend] using extendedGet
  have rightGet : (source.extend region).get rightIndex =
      expandWire input payload (target.get index) := by
    simpa [rightIndex, ConcreteElaboration.WireContext.extend] using
      embedding.get index
  apply Fin.ext
  exact (List.getElem_inj (i := leftIndex.val) (j := rightIndex.val)
    (h₀ := leftIndex.isLt) (h₁ := rightIndex.isLt) expandedNodup).mp (by
      simpa only [List.get_eq_getElem] using extendedGet'.trans rightGet.symm)

theorem extend_index_local
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (source : ConcreteElaboration.WireContext (Expanded input payload))
    (target : ConcreteElaboration.WireContext (Reduced input payload))
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount)
    (expandedNodup : (source.extend region).Nodup)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (Reduced input payload) region).length) :
    (embedding.extend region).index
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.natAdd target.length index)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend source region).symm
        (Fin.natAdd source.length
          ((localEmbedding input payload region).index index)) := by
  let leftIndex := (embedding.extend region).index
    (Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm
      (Fin.natAdd target.length index))
  let rightIndex := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source region).symm
    (Fin.natAdd source.length
      ((localEmbedding input payload region).index index))
  have extendedGet := (embedding.extend region).get
    (Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm
      (Fin.natAdd target.length index))
  have extendedGet' :
      (source.extend region).get leftIndex =
        expandWire input payload
          ((ConcreteElaboration.exactScopeWires
            (Reduced input payload) region).get index) := by
    simpa [leftIndex, ConcreteElaboration.WireContext.extend] using extendedGet
  have rightGet : (source.extend region).get rightIndex =
      expandWire input payload
        ((ConcreteElaboration.exactScopeWires
          (Reduced input payload) region).get index) := by
    simpa [rightIndex, ConcreteElaboration.WireContext.extend] using
      (localEmbedding input payload region).get index
  apply Fin.ext
  exact (List.getElem_inj (i := leftIndex.val) (j := rightIndex.val)
    (h₀ := leftIndex.isLt) (h₁ := rightIndex.isLt) expandedNodup).mp (by
      simpa only [List.get_eq_getElem] using extendedGet'.trans rightGet.symm)

theorem extendedEnvironments_agree
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (source : ConcreteElaboration.WireContext (Expanded input payload))
    (target : ConcreteElaboration.WireContext (Reduced input payload))
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount)
    (expandedNodup : (source.extend region).Nodup)
    (sourceOuter : Fin target.length → D)
    (targetOuter : Fin source.length → D)
    (outerAgrees : sourceOuter = targetOuter ∘ embedding.index)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      (Reduced input payload) region).length → D)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) region).length → D)
    (localAgrees : sourceLocal =
      targetLocal ∘ (localEmbedding input payload region).index) :
    ConcreteElaboration.extendedEnvironment target region sourceOuter sourceLocal =
      ConcreteElaboration.extendedEnvironment source region targetOuter targetLocal ∘
        (embedding.extend region).index := by
  funext combined
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend target region) combined
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm split =
        combined := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · simp only [Function.comp_apply]
    rw [extend_index_outer input payload source target embedding region
      expandedNodup outer]
    simp [ConcreteElaboration.extendedEnvironment, Diagram.extendWireEnv,
      outerAgrees, Function.comp_def]
  · simp only [Function.comp_apply]
    rw [extend_index_local input payload source target embedding region
      expandedNodup localIndex]
    simp [ConcreteElaboration.extendedEnvironment, Diagram.extendWireEnv,
      localAgrees, Function.comp_def]

noncomputable def regularInverseIndex (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) region).length) :
    Fin (ConcreteElaboration.exactScopeWires
      (Reduced input payload) region).length :=
  Classical.choose
    (localEmbedding_surjective_regular input payload region regular index)

theorem regularInverseIndex_spec (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) region).length) :
    (localEmbedding input payload region).index
        (regularInverseIndex input payload region regular index) = index :=
  Classical.choose_spec
    (localEmbedding_surjective_regular input payload region regular index)

theorem regularLocalSelection
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (direction : ConcreteElaboration.SimulationDirection)
    (source : ConcreteElaboration.WireContext (Expanded input payload))
    (target : ConcreteElaboration.WireContext (Reduced input payload))
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region)
    (expandedExact : (source.extend region).Exact region)
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin target.length → model.Carrier)
      (targetOuter : Fin source.length → model.Carrier),
      ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
          (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
          sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                (ConcreteElaboration.ContextIndexRelation.forwardMap
                  (embedding.extend region).index)
                (ConcreteElaboration.extendedEnvironment target region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment source region
                  targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                (ConcreteElaboration.ContextIndexRelation.forwardMap
                  (embedding.extend region).index)
                (ConcreteElaboration.extendedEnvironment target region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment source region
                  targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgreement
  have outerEq : sourceOuter = targetOuter ∘ embedding.index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceOuter targetOuter).mp outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal
      let targetLocal := fun index => sourceLocal
        (regularInverseIndex input payload region regular index)
      have localEq : sourceLocal =
          targetLocal ∘ (localEmbedding input payload region).index := by
        funext index
        have mapped := regularInverseIndex_spec input payload region regular
          ((localEmbedding input payload region).index index)
        have recovered := ContextEmbedding.index_injective
          (localEmbedding input payload region)
          (ConcreteElaboration.exactScopeWires_nodup
            (Reduced input payload) region) mapped
        simp [targetLocal, recovered]
      refine ⟨targetLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        (embedding.extend region).index _ _).mpr
      exact extendedEnvironments_agree input payload source target embedding
        region expandedExact.nodup sourceOuter targetOuter outerEq sourceLocal
        targetLocal localEq
  | backward =>
      intro targetLocal
      let sourceLocal :=
        targetLocal ∘ (localEmbedding input payload region).index
      refine ⟨sourceLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        (embedding.extend region).index _ _).mpr
      exact extendedEnvironments_agree input payload source target embedding
        region expandedExact.nodup sourceOuter targetOuter outerEq sourceLocal
        targetLocal rfl

noncomputable def focusedInverseIndex (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) payload.region).length)
    (notOutput :
      (ConcreteElaboration.exactScopeWires
        (Expanded input payload) payload.region).get index ≠
        Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    Fin (ConcreteElaboration.exactScopeWires
      (Reduced input payload) payload.region).length :=
  Classical.choose
    (localEmbedding_preimage_of_not_output input payload payload.region index
      notOutput)

theorem focusedInverseIndex_spec (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) payload.region).length)
    (notOutput :
      (ConcreteElaboration.exactScopeWires
        (Expanded input payload) payload.region).get index ≠
        Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    (localEmbedding input payload payload.region).index
        (focusedInverseIndex input payload index notOutput) = index :=
  Classical.choose_spec
    (localEmbedding_preimage_of_not_output input payload payload.region index
      notOutput)

noncomputable def focusedForwardLocal
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      (Reduced input payload) payload.region).length → D)
    (outputValue : D) :
    Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) payload.region).length → D :=
  fun index =>
    if output :
        (ConcreteElaboration.exactScopeWires
          (Expanded input payload) payload.region).get index =
          Fin.castAdd payload.argumentIndices.length payload.outputWire then
      outputValue
    else
      sourceLocal (focusedInverseIndex input payload index output)

theorem focusedForwardLocal_agrees
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      (Reduced input payload) payload.region).length → D)
    (outputValue : D) :
    sourceLocal =
      focusedForwardLocal input payload sourceLocal outputValue ∘
        (localEmbedding input payload payload.region).index := by
  funext index
  have mappedGet := (localEmbedding input payload payload.region).get index
  have notOutput :
      (ConcreteElaboration.exactScopeWires
        (Expanded input payload) payload.region).get
          ((localEmbedding input payload payload.region).index index) ≠
        Fin.castAdd payload.argumentIndices.length payload.outputWire := by
    rw [mappedGet]
    exact expandWire_not_output input payload _
  have recovered := ContextEmbedding.index_injective
    (localEmbedding input payload payload.region)
    (ConcreteElaboration.exactScopeWires_nodup
      (Reduced input payload) payload.region)
    (focusedInverseIndex_spec input payload
      ((localEmbedding input payload payload.region).index index) notOutput)
  change sourceLocal index = focusedForwardLocal input payload sourceLocal
    outputValue ((localEmbedding input payload payload.region).index index)
  unfold focusedForwardLocal
  rw [dif_neg notOutput]
  exact congrArg sourceLocal recovered.symm

noncomputable def focusedOutputIndex (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    Fin (ConcreteElaboration.exactScopeWires
      (Expanded input payload) payload.region).length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
    ((ConcreteElaboration.mem_exactScopeWires
      (Expanded input payload) payload.region
      (Fin.castAdd payload.argumentIndices.length payload.outputWire)).mpr (by
        simpa using payload.noAdditionalExistentialAttachment)))

theorem focusedOutputIndex_get (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    (ConcreteElaboration.exactScopeWires
      (Expanded input payload) payload.region).get
        (focusedOutputIndex input payload) =
      Fin.castAdd payload.argumentIndices.length payload.outputWire :=
  ConcreteElaboration.WireContext.lookup?_sound (Classical.choose_spec
    (ConcreteElaboration.WireContext.lookup?_complete
      ((ConcreteElaboration.mem_exactScopeWires
        (Expanded input payload) payload.region
        (Fin.castAdd payload.argumentIndices.length payload.outputWire)).mpr (by
          simpa using payload.noAdditionalExistentialAttachment))))

@[simp] theorem focusedForwardLocal_output
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      (Reduced input payload) payload.region).length → D)
    (outputValue : D) :
    focusedForwardLocal input payload sourceLocal outputValue
        (focusedOutputIndex input payload) = outputValue := by
  unfold focusedForwardLocal
  rw [dif_pos (focusedOutputIndex_get input payload)]

theorem focusedLocalSelection
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (direction : ConcreteElaboration.SimulationDirection)
    (source : ConcreteElaboration.WireContext (Expanded input payload))
    (target : ConcreteElaboration.WireContext (Reduced input payload))
    (embedding : ContextEmbedding input payload source target)
    (expandedExact : (source.extend payload.region).Exact payload.region)
    (model : Lambda.LambdaModel)
    (outputValue :
      (Fin (target.extend payload.region).length → model.Carrier) →
        model.Carrier) :
    ∀ (sourceOuter : Fin target.length → model.Carrier)
      (targetOuter : Fin source.length → model.Carrier),
      ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
          (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
          sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                (ConcreteElaboration.ContextIndexRelation.forwardMap
                  (embedding.extend payload.region).index)
                (ConcreteElaboration.extendedEnvironment target payload.region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment source payload.region
                  targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                (ConcreteElaboration.ContextIndexRelation.forwardMap
                  (embedding.extend payload.region).index)
                (ConcreteElaboration.extendedEnvironment target payload.region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment source payload.region
                  targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgreement
  have outerEq : sourceOuter = targetOuter ∘ embedding.index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceOuter targetOuter).mp outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal
      let sourceEnv := ConcreteElaboration.extendedEnvironment target
        payload.region sourceOuter sourceLocal
      let targetLocal := focusedForwardLocal input payload sourceLocal
        (outputValue sourceEnv)
      refine ⟨targetLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        (embedding.extend payload.region).index _ _).mpr
      exact extendedEnvironments_agree input payload source target embedding
        payload.region expandedExact.nodup sourceOuter targetOuter outerEq
        sourceLocal targetLocal
        (focusedForwardLocal_agrees input payload sourceLocal
          (outputValue sourceEnv))
  | backward =>
      intro targetLocal
      let sourceLocal :=
        targetLocal ∘ (localEmbedding input payload payload.region).index
      refine ⟨sourceLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        (embedding.extend payload.region).index _ _).mpr
      exact extendedEnvironments_agree input payload source target embedding
        payload.region expandedExact.nodup sourceOuter targetOuter outerEq
        sourceLocal targetLocal rfl

end HeadStripCompaction

end VisualProof.Rule
