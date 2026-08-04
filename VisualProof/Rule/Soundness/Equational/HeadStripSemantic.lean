import VisualProof.Rule.Equational
import VisualProof.Rule.Soundness.Congruence
import VisualProof.Diagram.Concrete.Elaboration.Simulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace HeadStripSoundness

theorem identityBinderWitness_relationMap_eq_identity
    {source target : ConcreteDiagram}
    {sourceBinders : ConcreteElaboration.BinderContext source rels}
    {targetBinders : ConcreteElaboration.BinderContext target rels}
    (witness : ConcreteElaboration.IdentityBinderWitness source target
      sourceBinders targetBinders) :
    (ConcreteElaboration.IdentityBinderWitness.relationMap witness :
      RelationRenaming rels rels) =
        (ConcreteElaboration.identityRelationRenaming rels :
          RelationRenaming rels rels) := by
  rcases witness with ⟨relationContextsEq, bindersEq⟩
  have equalityProof : relationContextsEq = rfl := Subsingleton.elim _ _
  cases equalityProof
  apply @funext
  intro arity
  funext relation
  rfl

theorem renameRelations_identityRelationRenaming
    (items : ItemSeq signature wires rels) :
    items.renameRelations
        (ConcreteElaboration.identityRelationRenaming rels) = items := by
  change items.renameRelations (fun relation => relation) = items
  exact ItemSeq.renameRelations_id items

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

@[simp] theorem headStripExpandedRaw_root
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    (headStripExpandedRaw input payload).root = input.val.root := rfl

@[simp] theorem headStripExpandedRaw_oldWire_scope
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) :
    ((headStripExpandedRaw input payload).wires
      (Fin.castAdd payload.argumentIndices.length wire)).scope =
        (input.val.wires wire).scope := by
  simp [headStripExpandedRaw]

@[simp] theorem headStripExpandedRaw_oldNode
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (node : Fin input.val.nodeCount) :
    (headStripExpandedRaw input payload).nodes
        (Fin.castAdd (payload.argumentIndices.length +
          payload.argumentIndices.length) node) =
      input.val.nodes node := by
  simp [headStripExpandedRaw]

theorem headStripExpandedRaw_oldEndpointOccurs_forward
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount)
    (node : Fin input.val.nodeCount) (port : CPort)
    (occurs : input.val.EndpointOccurs wire { node := node, port := port }) :
    (headStripExpandedRaw input payload).EndpointOccurs
      (Fin.castAdd payload.argumentIndices.length wire)
      { node := Fin.castAdd (payload.argumentIndices.length +
          payload.argumentIndices.length) node,
        port := port } := by
  unfold ConcreteDiagram.EndpointOccurs at occurs ⊢
  simp only [headStripExpandedRaw, Fin.addCases_left]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨{ node := node, port := port }, occurs, by
    simp [headStripLiftEndpoint]⟩

theorem headStripExpandedRaw_addedFreeEndpoint_node_fresh_first
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

theorem headStripExpandedRaw_addedFreeEndpoint_node_fresh_second
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

theorem headStripExpandedRaw_oldEndpointOccurs_backward
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWire : Fin (headStripExpandedRaw input payload).wireCount)
    (node : Fin input.val.nodeCount) (port : CPort)
    (occurs : (headStripExpandedRaw input payload).EndpointOccurs targetWire
      { node := Fin.castAdd (payload.argumentIndices.length +
          payload.argumentIndices.length) node,
        port := port }) :
    ∃ wire,
      Fin.castAdd payload.argumentIndices.length wire = targetWire ∧
        input.val.EndpointOccurs wire { node := node, port := port } := by
  refine Fin.addCases (motive := fun targetWire =>
      (headStripExpandedRaw input payload).EndpointOccurs targetWire
        { node := Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length) node, port := port } →
      ∃ wire,
        Fin.castAdd payload.argumentIndices.length wire = targetWire ∧
          input.val.EndpointOccurs wire { node := node, port := port })
    (fun wire occurrence => ?_)
    (fun position occurrence => ?_) targetWire occurs
  · unfold ConcreteDiagram.EndpointOccurs at occurrence ⊢
    simp only [headStripExpandedRaw, Fin.addCases_left] at occurrence
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
    · have fresh := headStripExpandedRaw_addedFreeEndpoint_node_fresh_first
        payload wire _ firstAdded
      change input.val.nodeCount ≤ node.val at fresh
      omega
    · have fresh := headStripExpandedRaw_addedFreeEndpoint_node_fresh_second
        payload wire _ secondAdded
      change input.val.nodeCount ≤ node.val at fresh
      omega
  · unfold ConcreteDiagram.EndpointOccurs at occurrence
    simp only [headStripExpandedRaw, Fin.addCases_right] at occurrence
    change (⟨Fin.castAdd
        (payload.argumentIndices.length + payload.argumentIndices.length) node,
          port⟩ : CEndpoint (headStripExpandedRaw input payload).nodeCount) ∈
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

theorem headStripExpandedRaw_exactScopeWires
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) :
    ConcreteElaboration.exactScopeWires (headStripExpandedRaw input payload) region =
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
    rw [headStripExpandedRaw_oldWire_scope]
    rfl
  · split <;> rename_i hregion
    · subst region
      apply congrArg (List.map (Fin.natAdd input.val.wireCount))
      apply List.filter_eq_self.mpr
      intro wire _
      simp [headStripExpandedRaw]
    · change List.map (Fin.natAdd input.val.wireCount)
          (List.filter _ (allFin payload.argumentIndices.length)) = []
      apply (List.map_eq_nil_iff).mpr
      apply List.filter_eq_nil_iff.mpr
      intro wire _ equality
      have decided : decide
          (((headStripExpandedRaw input payload).wires
            (Fin.natAdd input.val.wireCount wire)).scope = region) = true :=
        equality
      simp only [decide_eq_true_eq, headStripExpandedRaw, Fin.addCases_right] at decided
      exact hregion decided.symm

def liftOccurrence
    (payload : HeadStripPayload input first second)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount) :
    ConcreteElaboration.LocalOccurrence (headStripExpandedRaw input payload).regionCount
      (headStripExpandedRaw input payload).nodeCount :=
  match occurrence with
  | .node node => .node (Fin.castAdd
      (payload.argumentIndices.length + payload.argumentIndices.length) node)
  | .child child => .child child

theorem headStripExpandedRaw_regular_localOccurrences
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region) :
    ConcreteElaboration.localOccurrences (headStripExpandedRaw input payload) region =
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
      ((headStripExpandedRaw input payload).nodes
        (Fin.natAdd input.val.nodeCount node)).region ≠ region := by
    intro node
    refine Fin.addCases (motive := fun node =>
        ((headStripExpandedRaw input payload).nodes
          (Fin.natAdd input.val.nodeCount node)).region ≠ region)
      (fun position equality => ?_) (fun position equality => ?_) node
    · apply regular
      simpa only [headStripExpandedRaw, Fin.addCases_right, Fin.addCases_left,
        CNode.region] using equality.symm
    · apply regular
      simpa only [headStripExpandedRaw, Fin.addCases_right, CNode.region] using
        equality.symm
  have freshEmpty :
      List.filter
        ((fun node => decide (((headStripExpandedRaw input payload).nodes node).region =
          region)) ∘ Fin.natAdd input.val.nodeCount)
        (allFin (payload.argumentIndices.length +
          payload.argumentIndices.length)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro node _ member
    exact freshFalse node (of_decide_eq_true member)
  have oldFilter :
      List.filter
        ((fun node => decide (((headStripExpandedRaw input payload).nodes node).region =
          region)) ∘ Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length))
        (allFin input.val.nodeCount) =
      List.filter (fun node => decide ((input.val.nodes node).region = region))
        (allFin input.val.nodeCount) := by
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.val.nodeCount))
    funext node
    simp only [Function.comp_apply, headStripExpandedRaw_oldNode]
    rfl
  dsimp only [headStripExpandedRaw] at freshEmpty oldFilter ⊢
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
      (headStripExpandedRaw input payload).regionCount
      (headStripExpandedRaw input payload).nodeCount) :=
  (allFin payload.argumentIndices.length).map fun position =>
    .node (payload.firstAddedNode position)

def secondAddedOccurrences
    (payload : HeadStripPayload input first second) :
    List (ConcreteElaboration.LocalOccurrence
      (headStripExpandedRaw input payload).regionCount
      (headStripExpandedRaw input payload).nodeCount) :=
  (allFin payload.argumentIndices.length).map fun position =>
    .node (payload.secondAddedNode position)

theorem source_localOccurrences
    (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount) :
    ConcreteElaboration.localOccurrences input.val region =
      sourceNodeOccurrences input region ++ sourceChildOccurrences input region :=
  rfl

theorem headStripExpandedRaw_focused_localOccurrences
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    ConcreteElaboration.localOccurrences (headStripExpandedRaw input payload)
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
        ((fun node => decide (((headStripExpandedRaw input payload).nodes node).region =
          payload.region)) ∘ Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length))
        (allFin input.val.nodeCount) =
      filterFin fun node =>
        decide ((input.val.nodes node).region = payload.region) := by
    unfold filterFin
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.val.nodeCount))
    funext node
    simp only [Function.comp_apply, headStripExpandedRaw_oldNode]
    rfl
  have firstFilter :
      List.filter
        (((fun node => decide (((headStripExpandedRaw input payload).nodes node).region =
          payload.region)) ∘ Fin.natAdd input.val.nodeCount) ∘
            Fin.castAdd payload.argumentIndices.length)
        (allFin payload.argumentIndices.length) =
      allFin payload.argumentIndices.length := by
    apply List.filter_eq_self.mpr
    intro position member
    simp only [Function.comp_apply, headStripExpandedRaw, Fin.addCases_right,
      Fin.addCases_left, CNode.region, decide_true]
  have secondFilter :
      List.filter
        (((fun node => decide (((headStripExpandedRaw input payload).nodes node).region =
          payload.region)) ∘ Fin.natAdd input.val.nodeCount) ∘
            Fin.natAdd payload.argumentIndices.length)
        (allFin payload.argumentIndices.length) =
      allFin payload.argumentIndices.length := by
    apply List.filter_eq_self.mpr
    intro position member
    simp only [Function.comp_apply, headStripExpandedRaw, Fin.addCases_right,
      CNode.region, decide_true]
  have childFilter :
      List.filter
        (fun child => decide (((headStripExpandedRaw input payload).regions child).parent? =
          some payload.region)) (allFin input.val.regionCount) =
    filterFin fun child =>
        decide ((input.val.regions child).parent? = some payload.region) := by
    rfl
  dsimp only [headStripExpandedRaw] at oldFilter firstFilter secondFilter childFilter ⊢
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
      (headStripExpandedRaw input payload).regionCount
      (headStripExpandedRaw input payload).nodeCount) ∘
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
      (headStripExpandedRaw input payload).regionCount
      (headStripExpandedRaw input payload).nodeCount) ∘ Fin.natAdd input.val.nodeCount) ∘
      Fin.castAdd payload.argumentIndices.length)
    (allFin payload.argumentIndices.length)
  let firstSource := List.map (fun position =>
      (@ConcreteElaboration.LocalOccurrence.node
        (headStripExpandedRaw input payload).regionCount
        (headStripExpandedRaw input payload).nodeCount)
        (payload.firstAddedNode position))
    (allFin payload.argumentIndices.length)
  let secondTarget := List.map
    (((@ConcreteElaboration.LocalOccurrence.node
      (headStripExpandedRaw input payload).regionCount
      (headStripExpandedRaw input payload).nodeCount) ∘ Fin.natAdd input.val.nodeCount) ∘
      Fin.natAdd payload.argumentIndices.length)
    (allFin payload.argumentIndices.length)
  let secondSource := List.map (fun position =>
      (@ConcreteElaboration.LocalOccurrence.node
        (headStripExpandedRaw input payload).regionCount
        (headStripExpandedRaw input payload).nodeCount)
        (payload.secondAddedNode position))
    (allFin payload.argumentIndices.length)
  let childTarget := List.map
    (@ConcreteElaboration.LocalOccurrence.child
      (headStripExpandedRaw input payload).regionCount
      (headStripExpandedRaw input payload).nodeCount)
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
    (target : ConcreteElaboration.WireContext (headStripExpandedRaw input payload)) where
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
    {target : ConcreteElaboration.WireContext (headStripExpandedRaw input payload)}
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
          (headStripExpandedRaw input payload) region
          (Fin.castAdd payload.argumentIndices.length wire)).mp localScope
        simpa using scope
    · intro member
      rcases List.mem_append.mp member with inherited | localScope
      · exact List.mem_append_left _ ((embedding.mem_old wire).mpr inherited)
      · apply List.mem_append_right
        apply (ConcreteElaboration.mem_exactScopeWires
          (headStripExpandedRaw input payload) region
          (Fin.castAdd payload.argumentIndices.length wire)).mpr
        have scope := (ConcreteElaboration.mem_exactScopeWires input.val region
          wire).mp localScope
        simpa using scope)

end ContextEmbedding

theorem focusedExactScopeLength
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    (ConcreteElaboration.exactScopeWires (headStripExpandedRaw input payload)
        payload.region).length =
      (ConcreteElaboration.exactScopeWires input.val payload.region).length +
        payload.argumentIndices.length := by
  rw [headStripExpandedRaw_exactScopeWires]
  simp only [if_pos]
  calc
    (List.map (Fin.castAdd payload.argumentIndices.length)
          (ConcreteElaboration.exactScopeWires input.val payload.region) ++
        List.map (Fin.natAdd input.val.wireCount)
          (allFin payload.argumentIndices.length)).length =
      (ConcreteElaboration.exactScopeWires input.val payload.region).length +
        (allFin payload.argumentIndices.length).length := by
          rw [List.length_append, List.length_map, List.length_map]
    _ = (ConcreteElaboration.exactScopeWires input.val payload.region).length +
        payload.argumentIndices.length := by
      rw [allFin_eq_finRange, List.length_finRange]

noncomputable def extendedWireMapAtFocus
    (embedding : ContextEmbedding input payload source target) :
    Fin (source.extend payload.region).length →
      Fin (target.extend payload.region).length :=
  fun index =>
    Fin.cast (ConcreteElaboration.WireContext.length_extend
      target payload.region).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (ConcreteElaboration.exactScopeWires
            (headStripExpandedRaw input payload) payload.region).length
          (embedding.index outer))
        (fun localIndex => Fin.natAdd target.length
          (Fin.cast (focusedExactScopeLength input payload).symm
            (Fin.castAdd payload.argumentIndices.length localIndex)))
        (Fin.cast (ConcreteElaboration.WireContext.length_extend
          source payload.region) index))

theorem extendedWireMapAtFocus_spec
    (embedding : ContextEmbedding input payload source target)
    (index : Fin (source.extend payload.region).length) :
    (target.extend payload.region).get
        (extendedWireMapAtFocus embedding index) =
      Fin.castAdd payload.argumentIndices.length
        ((source.extend payload.region).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source payload.region) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        source payload.region).symm split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have mapped : extendedWireMapAtFocus embedding
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            source payload.region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.val
              payload.region).length outer)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          target payload.region).symm
        (Fin.castAdd
          (ConcreteElaboration.exactScopeWires
            (headStripExpandedRaw input payload) payload.region).length
          (embedding.index outer)) := by
      apply Fin.ext
      simp [extendedWireMapAtFocus]
    rw [mapped]
    simpa [ConcreteElaboration.WireContext.extend] using embedding.get outer
  · let lengthEq := focusedExactScopeLength input payload
    have mapped : extendedWireMapAtFocus embedding
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            source payload.region).symm
          (Fin.natAdd source.length localIndex)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          target payload.region).symm
        (Fin.natAdd target.length
          (Fin.cast lengthEq.symm
            (Fin.castAdd payload.argumentIndices.length localIndex))) := by
      apply Fin.ext
      simp [extendedWireMapAtFocus]
    rw [mapped]
    have exactWires := headStripExpandedRaw_exactScopeWires input payload payload.region
    simp [ConcreteElaboration.WireContext.extend, exactWires]
    change
      (List.map (Fin.castAdd payload.argumentIndices.length)
          (ConcreteElaboration.exactScopeWires input.val payload.region) ++
        List.map (Fin.natAdd input.val.wireCount)
          (allFin payload.argumentIndices.length))[localIndex.val] =
      Fin.castAdd payload.argumentIndices.length
        (ConcreteElaboration.exactScopeWires input.val
          payload.region)[localIndex.val]
    rw [List.getElem_append_left (by
      rw [List.length_map]
      exact localIndex.isLt)]
    exact List.getElem_map _

theorem ContextEmbedding.extend_index_eq_map_at_focus
    (embedding : ContextEmbedding input payload source target)
    (targetNodup : (target.extend payload.region).Nodup)
    (index : Fin (source.extend payload.region).length) :
    (embedding.extend payload.region).index index =
      extendedWireMapAtFocus embedding index := by
  symm
  apply Fin.ext
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using
      (extendedWireMapAtFocus_spec embedding index).trans
        ((embedding.extend payload.region).get index).symm)

def focusedForwardLocal
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      payload.region).length → D)
    (fresh : Fin payload.argumentIndices.length → D) :
    Fin (ConcreteElaboration.exactScopeWires (headStripExpandedRaw input payload)
      payload.region).length → D :=
  fun index =>
    Fin.addCases sourceLocal fresh
      (Fin.cast (focusedExactScopeLength input payload) index)

def focusedBackwardLocal
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (headStripExpandedRaw input payload) payload.region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires input.val
      payload.region).length → D :=
  fun index => targetLocal
    (Fin.cast (focusedExactScopeLength input payload).symm
      (Fin.castAdd payload.argumentIndices.length index))

theorem focusedForwardExtendedEnvironment
    (embedding : ContextEmbedding input payload source target)
    (sourceOuter : Fin source.length → D)
    (targetOuter : Fin target.length → D)
    (outerAgrees : sourceOuter = targetOuter ∘ embedding.index)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      payload.region).length → D)
    (fresh : Fin payload.argumentIndices.length → D)
    (targetNodup : (target.extend payload.region).Nodup) :
    ConcreteElaboration.extendedEnvironment source payload.region
        sourceOuter sourceLocal =
      ConcreteElaboration.extendedEnvironment target payload.region
          targetOuter (focusedForwardLocal input payload sourceLocal fresh) ∘
        (embedding.extend payload.region).index := by
  rw [outerAgrees]
  funext index
  simp only [Function.comp_apply]
  rw [embedding.extend_index_eq_map_at_focus targetNodup]
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source payload.region) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        source payload.region).symm split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · simp [ConcreteElaboration.extendedEnvironment, extendedWireMapAtFocus,
      Diagram.extendWireEnv, Function.comp_def]
  · simp [ConcreteElaboration.extendedEnvironment, extendedWireMapAtFocus,
      focusedForwardLocal, Diagram.extendWireEnv, Function.comp_def]

theorem focusedBackwardExtendedEnvironment
    (embedding : ContextEmbedding input payload source target)
    (sourceOuter : Fin source.length → D)
    (targetOuter : Fin target.length → D)
    (outerAgrees : sourceOuter = targetOuter ∘ embedding.index)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (headStripExpandedRaw input payload) payload.region).length → D)
    (targetNodup : (target.extend payload.region).Nodup) :
    ConcreteElaboration.extendedEnvironment source payload.region sourceOuter
        (focusedBackwardLocal input payload targetLocal) =
      ConcreteElaboration.extendedEnvironment target payload.region targetOuter
          targetLocal ∘ (embedding.extend payload.region).index := by
  rw [outerAgrees]
  funext index
  simp only [Function.comp_apply]
  rw [embedding.extend_index_eq_map_at_focus targetNodup]
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source payload.region) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        source payload.region).symm split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · simp [ConcreteElaboration.extendedEnvironment, extendedWireMapAtFocus,
      Diagram.extendWireEnv, Function.comp_def]
  · simp [ConcreteElaboration.extendedEnvironment, extendedWireMapAtFocus,
      focusedBackwardLocal, Diagram.extendWireEnv, Function.comp_def]

@[simp] theorem headStripExpandedRaw_firstAddedNode
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    (headStripExpandedRaw input payload).nodes (payload.firstAddedNode position) =
      .term payload.region
        (payload.firstArgument
          (payload.argumentIndices.get position)).freeSupport.length
        (payload.firstArgument
          (payload.argumentIndices.get position)).compact := by
  simp [headStripExpandedRaw, HeadStripPayload.firstAddedNode]

@[simp] theorem headStripExpandedRaw_secondAddedNode
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    (headStripExpandedRaw input payload).nodes (payload.secondAddedNode position) =
      .term payload.region
        (payload.secondArgument
          (payload.argumentIndices.get position)).freeSupport.length
        (payload.secondArgument
          (payload.argumentIndices.get position)).compact := by
  simp only [headStripExpandedRaw, HeadStripPayload.secondAddedNode,
    Fin.addCases_right]

theorem headStripExpandedRaw_firstAddedOutput_occurs
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    (headStripExpandedRaw input payload).EndpointOccurs
      (Fin.natAdd input.val.wireCount position)
      { node := payload.firstAddedNode position, port := .output } := by
  unfold ConcreteDiagram.EndpointOccurs
  simp only [headStripExpandedRaw, Fin.addCases_right]
  exact List.mem_cons_self

theorem headStripExpandedRaw_secondAddedOutput_occurs
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    (headStripExpandedRaw input payload).EndpointOccurs
      (Fin.natAdd input.val.wireCount position)
      { node := payload.secondAddedNode position, port := .output } := by
  unfold ConcreteDiagram.EndpointOccurs
  simp only [headStripExpandedRaw, Fin.addCases_right]
  exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))

theorem headStripExpandedRaw_firstAddedFree_occurs
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length)
    (port : Fin (payload.firstArgument
      (payload.argumentIndices.get position)).freeSupport.length) :
    (headStripExpandedRaw input payload).EndpointOccurs
      (Fin.castAdd payload.argumentIndices.length
        (payload.firstWire ((payload.firstArgument
          (payload.argumentIndices.get position)).freeSupport.get port)))
      { node := payload.firstAddedNode position, port := .free port } := by
  unfold ConcreteDiagram.EndpointOccurs
  simp only [headStripExpandedRaw, Fin.addCases_left]
  apply List.mem_append_left
  apply List.mem_append_right
  unfold HeadStripPayload.firstAddedFreeEndpoints
  apply List.mem_flatMap.mpr
  refine ⟨position, mem_allFin position, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨port, mem_allFin port, ?_⟩
  simp

theorem headStripExpandedRaw_secondAddedFree_occurs
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length)
    (port : Fin (payload.secondArgument
      (payload.argumentIndices.get position)).freeSupport.length) :
    (headStripExpandedRaw input payload).EndpointOccurs
      (Fin.castAdd payload.argumentIndices.length
        (payload.secondWire ((payload.secondArgument
          (payload.argumentIndices.get position)).freeSupport.get port)))
      { node := payload.secondAddedNode position, port := .free port } := by
  unfold ConcreteDiagram.EndpointOccurs
  simp only [headStripExpandedRaw, Fin.addCases_left]
  apply List.mem_append_right
  unfold HeadStripPayload.secondAddedFreeEndpoints
  apply List.mem_flatMap.mpr
  refine ⟨position, mem_allFin position, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨port, mem_allFin port, ?_⟩
  simp

theorem firstAddedNode_denote
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature)
    (context : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (binders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) rels)
    (position : Fin payload.argumentIndices.length)
    (item : Item signature context.length rels)
    (compiled : ConcreteElaboration.compileNode? signature
      (headStripExpandedRaw input payload) context binders
      (payload.firstAddedNode position) = some item)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (env : Fin context.length → Lambda.Individual)
    (outputValue : ∀ index, context.get index =
        Fin.natAdd input.val.wireCount position →
      env index = Lambda.canonicalModel.eval
        ((payload.firstArgument
          (payload.argumentIndices.get position)).mapFree payload.firstPort)
        common)
    (freeValue : ∀ port index, context.get index =
        Fin.castAdd payload.argumentIndices.length (payload.firstWire port) →
      env index = common (payload.firstPort port))
    (named : NamedEnv Lambda.Individual signature)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItem Lambda.canonicalModel named env relEnv item := by
  let argument := payload.firstArgument (payload.argumentIndices.get position)
  have nodeShape : (headStripExpandedRaw input payload).nodes
      (payload.firstAddedNode position) =
    .term payload.region argument.freeSupport.length argument.compact := by
    simpa only [argument] using headStripExpandedRaw_firstAddedNode payload position
  simp only [ConcreteElaboration.compileNode?, nodeShape] at compiled
  cases outputResult : ConcreteElaboration.resolvePort?
      (headStripExpandedRaw input payload) context (payload.firstAddedNode position)
      .output with
  | none =>
      simp [outputResult] at compiled
  | some output =>
      cases freeResult : ConcreteElaboration.resolvePorts?
          (headStripExpandedRaw input payload) context (payload.firstAddedNode position)
          argument.freeSupport.length (fun port => .free port) with
      | none =>
          simp [outputResult, freeResult] at compiled
      | some free =>
          simp [outputResult, freeResult] at compiled
          subst item
          obtain ⟨outputWire, outputOccurs, outputGet⟩ :=
            ConcreteElaboration.resolvePort?_sound outputResult
          have outputWireEq : outputWire =
              Fin.natAdd input.val.wireCount position :=
            ConcreteElaboration.endpoint_wire_unique
              targetWellFormed.wire_endpoints_are_disjoint outputOccurs
                (headStripExpandedRaw_firstAddedOutput_occurs payload position)
          have outputEquation := outputValue output (by
            simpa only [List.get_eq_getElem, outputWireEq] using outputGet)
          have freeEnvironment : env ∘ free =
              (common ∘ payload.firstPort) ∘ argument.freeSupport.get := by
            funext port
            have resolved := sequenceFin_sound freeResult port
            obtain ⟨wire, occurs, getWire⟩ :=
              ConcreteElaboration.resolvePort?_sound resolved
            have wireEq : wire = Fin.castAdd payload.argumentIndices.length
                (payload.firstWire (argument.freeSupport.get port)) :=
              ConcreteElaboration.endpoint_wire_unique
                targetWellFormed.wire_endpoints_are_disjoint occurs
                  (headStripExpandedRaw_firstAddedFree_occurs payload position port)
            simpa only [Function.comp_apply] using freeValue
              (argument.freeSupport.get port) (free port) (by
                simpa only [List.get_eq_getElem, wireEq] using getWire)
          rw [denoteItem_equation, outputEquation,
            Lambda.LambdaModel.eval_mapFree]
          rw [Lambda.LambdaModel.eval_mapFree]
          exact (LambdaModel.eval_compact Lambda.canonicalModel argument
            (common ∘ payload.firstPort)).symm.trans
              (congrArg
                (fun environment =>
                  Lambda.canonicalModel.eval argument.compact environment)
                freeEnvironment.symm)

theorem secondAddedNode_denote
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature)
    (context : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (binders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) rels)
    (position : Fin payload.argumentIndices.length)
    (item : Item signature context.length rels)
    (compiled : ConcreteElaboration.compileNode? signature
      (headStripExpandedRaw input payload) context binders
      (payload.secondAddedNode position) = some item)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (env : Fin context.length → Lambda.Individual)
    (outputValue : ∀ index, context.get index =
        Fin.natAdd input.val.wireCount position →
      env index = Lambda.canonicalModel.eval
        ((payload.secondArgument
          (payload.argumentIndices.get position)).mapFree payload.secondPort)
        common)
    (freeValue : ∀ port index, context.get index =
        Fin.castAdd payload.argumentIndices.length (payload.secondWire port) →
      env index = common (payload.secondPort port))
    (named : NamedEnv Lambda.Individual signature)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItem Lambda.canonicalModel named env relEnv item := by
  let argument := payload.secondArgument (payload.argumentIndices.get position)
  have nodeShape : (headStripExpandedRaw input payload).nodes
      (payload.secondAddedNode position) =
    .term payload.region argument.freeSupport.length argument.compact := by
    simpa only [argument] using headStripExpandedRaw_secondAddedNode payload position
  simp only [ConcreteElaboration.compileNode?, nodeShape] at compiled
  cases outputResult : ConcreteElaboration.resolvePort?
      (headStripExpandedRaw input payload) context (payload.secondAddedNode position)
      .output with
  | none =>
      simp [outputResult] at compiled
  | some output =>
      cases freeResult : ConcreteElaboration.resolvePorts?
          (headStripExpandedRaw input payload) context (payload.secondAddedNode position)
          argument.freeSupport.length (fun port => .free port) with
      | none =>
          simp [outputResult, freeResult] at compiled
      | some free =>
          simp [outputResult, freeResult] at compiled
          subst item
          obtain ⟨outputWire, outputOccurs, outputGet⟩ :=
            ConcreteElaboration.resolvePort?_sound outputResult
          have outputWireEq : outputWire =
              Fin.natAdd input.val.wireCount position :=
            ConcreteElaboration.endpoint_wire_unique
              targetWellFormed.wire_endpoints_are_disjoint outputOccurs
                (headStripExpandedRaw_secondAddedOutput_occurs payload position)
          have outputEquation := outputValue output (by
            simpa only [List.get_eq_getElem, outputWireEq] using outputGet)
          have freeEnvironment : env ∘ free =
              (common ∘ payload.secondPort) ∘ argument.freeSupport.get := by
            funext port
            have resolved := sequenceFin_sound freeResult port
            obtain ⟨wire, occurs, getWire⟩ :=
              ConcreteElaboration.resolvePort?_sound resolved
            have wireEq : wire = Fin.castAdd payload.argumentIndices.length
                (payload.secondWire (argument.freeSupport.get port)) :=
              ConcreteElaboration.endpoint_wire_unique
                targetWellFormed.wire_endpoints_are_disjoint occurs
                  (headStripExpandedRaw_secondAddedFree_occurs payload position port)
            simpa only [Function.comp_apply] using freeValue
              (argument.freeSupport.get port) (free port) (by
                simpa only [List.get_eq_getElem, wireEq] using getWire)
          rw [denoteItem_equation, outputEquation,
            Lambda.LambdaModel.eval_mapFree]
          rw [Lambda.LambdaModel.eval_mapFree]
          exact (LambdaModel.eval_compact Lambda.canonicalModel argument
            (common ∘ payload.secondPort)).symm.trans
              (congrArg
                (fun environment =>
                  Lambda.canonicalModel.eval argument.compact environment)
                freeEnvironment.symm)

theorem firstAddedOccurrences_denote
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature)
    (recurse : ∀ {relations : RelCtx},
      Fin (headStripExpandedRaw input payload).regionCount →
      (recurseContext : ConcreteElaboration.WireContext
        (headStripExpandedRaw input payload)) →
      ConcreteElaboration.BinderContext
        (headStripExpandedRaw input payload) relations →
      Option (Region signature recurseContext.length relations))
    (context : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (binders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) rels)
    (positions : List (Fin payload.argumentIndices.length))
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (headStripExpandedRaw input payload) recurse context binders
      (positions.map fun position =>
        ConcreteElaboration.LocalOccurrence.node
          (payload.firstAddedNode position)) = some items)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (env : Fin context.length → Lambda.Individual)
    (outputValue : ∀ position index, context.get index =
        Fin.natAdd input.val.wireCount position →
      env index = Lambda.canonicalModel.eval
        ((payload.firstArgument
          (payload.argumentIndices.get position)).mapFree payload.firstPort)
        common)
    (freeValue : ∀ port index, context.get index =
        Fin.castAdd payload.argumentIndices.length (payload.firstWire port) →
      env index = common (payload.firstPort port))
    (named : NamedEnv Lambda.Individual signature)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItemSeq Lambda.canonicalModel named env relEnv items := by
  induction positions generalizing items with
  | nil =>
      simp [ConcreteElaboration.compileOccurrencesWith?] at compiled
      subst items
      exact True.intro
  | cons position rest induction =>
      simp only [List.map_cons, ConcreteElaboration.compileOccurrencesWith?]
        at compiled
      cases headResult : ConcreteElaboration.compileNode? signature
          (headStripExpandedRaw input payload) context binders
          (payload.firstAddedNode position) with
      | none => simp [ConcreteElaboration.compileOccurrenceWith?, headResult]
          at compiled
      | some head =>
          cases tailResult : ConcreteElaboration.compileOccurrencesWith?
              signature (headStripExpandedRaw input payload) recurse context binders
              (rest.map fun current =>
                ConcreteElaboration.LocalOccurrence.node
                  (payload.firstAddedNode current)) with
          | none => simp [ConcreteElaboration.compileOccurrenceWith?, headResult,
              tailResult] at compiled
          | some tail =>
              simp [ConcreteElaboration.compileOccurrenceWith?, headResult,
                tailResult] at compiled
              subst items
              rw [denoteItemSeq_cons]
              exact ⟨firstAddedNode_denote input payload targetWellFormed
                context binders position head headResult common env
                (outputValue position) freeValue named relEnv,
                induction tail tailResult⟩

theorem secondAddedOccurrences_denote
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature)
    (recurse : ∀ {relations : RelCtx},
      Fin (headStripExpandedRaw input payload).regionCount →
      (recurseContext : ConcreteElaboration.WireContext
        (headStripExpandedRaw input payload)) →
      ConcreteElaboration.BinderContext
        (headStripExpandedRaw input payload) relations →
      Option (Region signature recurseContext.length relations))
    (context : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (binders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) rels)
    (positions : List (Fin payload.argumentIndices.length))
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (headStripExpandedRaw input payload) recurse context binders
      (positions.map fun position =>
        ConcreteElaboration.LocalOccurrence.node
          (payload.secondAddedNode position)) = some items)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (env : Fin context.length → Lambda.Individual)
    (outputValue : ∀ position index, context.get index =
        Fin.natAdd input.val.wireCount position →
      env index = Lambda.canonicalModel.eval
        ((payload.secondArgument
          (payload.argumentIndices.get position)).mapFree payload.secondPort)
        common)
    (freeValue : ∀ port index, context.get index =
        Fin.castAdd payload.argumentIndices.length (payload.secondWire port) →
      env index = common (payload.secondPort port))
    (named : NamedEnv Lambda.Individual signature)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItemSeq Lambda.canonicalModel named env relEnv items := by
  induction positions generalizing items with
  | nil =>
      simp [ConcreteElaboration.compileOccurrencesWith?] at compiled
      subst items
      exact True.intro
  | cons position rest induction =>
      simp only [List.map_cons, ConcreteElaboration.compileOccurrencesWith?]
        at compiled
      cases headResult : ConcreteElaboration.compileNode? signature
          (headStripExpandedRaw input payload) context binders
          (payload.secondAddedNode position) with
      | none => simp [ConcreteElaboration.compileOccurrenceWith?, headResult]
          at compiled
      | some head =>
          cases tailResult : ConcreteElaboration.compileOccurrencesWith?
              signature (headStripExpandedRaw input payload) recurse context binders
              (rest.map fun current =>
                ConcreteElaboration.LocalOccurrence.node
                  (payload.secondAddedNode current)) with
          | none => simp [ConcreteElaboration.compileOccurrenceWith?, headResult,
              tailResult] at compiled
          | some tail =>
              simp [ConcreteElaboration.compileOccurrenceWith?, headResult,
                tailResult] at compiled
              subst items
              rw [denoteItemSeq_cons]
              exact ⟨secondAddedNode_denote input payload targetWellFormed
                context binders position head headResult common env
                (outputValue position) freeValue named relEnv,
                induction tail tailResult⟩

def focusedFreshLocalIndex
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    Fin (ConcreteElaboration.exactScopeWires (headStripExpandedRaw input payload)
      payload.region).length :=
  Fin.cast (focusedExactScopeLength input payload).symm
    (Fin.natAdd
      (ConcreteElaboration.exactScopeWires input.val payload.region).length
      position)

def focusedFreshExtendedIndex
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (position : Fin payload.argumentIndices.length) :
    Fin (context.extend payload.region).length :=
  Fin.cast (ConcreteElaboration.WireContext.length_extend
      context payload.region).symm
    (Fin.natAdd context.length
      (focusedFreshLocalIndex input payload position))

theorem focusedFreshExtendedIndex_get
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (position : Fin payload.argumentIndices.length) :
    (context.extend payload.region).get
        (focusedFreshExtendedIndex input payload context position) =
      Fin.natAdd input.val.wireCount position := by
  have localGet := ConcreteElaboration.WireContext.extend_local context
    payload.region (focusedFreshLocalIndex input payload position)
  rw [show (context.extend payload.region).get
      (focusedFreshExtendedIndex input payload context position) =
        (ConcreteElaboration.exactScopeWires (headStripExpandedRaw input payload)
          payload.region).get
            (focusedFreshLocalIndex input payload position) by
      simpa [focusedFreshExtendedIndex] using localGet]
  let oldWires := List.map (Fin.castAdd payload.argumentIndices.length)
    (ConcreteElaboration.exactScopeWires input.val payload.region)
  let freshWires := List.map (Fin.natAdd input.val.wireCount)
    (allFin payload.argumentIndices.length)
  have exactWires : ConcreteElaboration.exactScopeWires
      (headStripExpandedRaw input payload) payload.region = oldWires ++ freshWires := by
    simpa [oldWires, freshWires] using
      headStripExpandedRaw_exactScopeWires input payload payload.region
  let rightIndex : Fin (oldWires ++ freshWires).length :=
    ⟨oldWires.length + position.val, by
      simp [oldWires, freshWires, allFin_eq_finRange]⟩
  have transported := List.get_of_eq exactWires
    (focusedFreshLocalIndex input payload position)
  have castEq : Fin.cast (congrArg List.length exactWires)
      (focusedFreshLocalIndex input payload position) = rightIndex := by
    apply Fin.ext
    simp [rightIndex, oldWires, focusedFreshLocalIndex]
  rw [transported]
  let transportedIndex : Fin (oldWires ++ freshWires).length :=
    ⟨(focusedFreshLocalIndex input payload position).val, by
      exact (Fin.cast (congrArg List.length exactWires)
        (focusedFreshLocalIndex input payload position)).isLt⟩
  change (oldWires ++ freshWires).get transportedIndex = _
  have transportedIndexEq : transportedIndex = rightIndex := by
    apply Fin.ext
    exact congrArg Fin.val castEq
  rw [transportedIndexEq]
  simp [rightIndex, freshWires, allFin_eq_finRange]

theorem focusedForward_fresh_value
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (outer : Fin context.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      payload.region).length → D)
    (fresh : Fin payload.argumentIndices.length → D)
    (nodup : (context.extend payload.region).Nodup)
    (position : Fin payload.argumentIndices.length)
    (index : Fin (context.extend payload.region).length)
    (indexGet : (context.extend payload.region).get index =
      Fin.natAdd input.val.wireCount position) :
    ConcreteElaboration.extendedEnvironment context payload.region outer
        (focusedForwardLocal input payload sourceLocal fresh) index =
      fresh position := by
  have freshGet := focusedFreshExtendedIndex_get input payload context position
  have indexEq : index =
      focusedFreshExtendedIndex input payload context position := by
    apply Fin.ext
    exact (List.getElem_inj nodup).mp (by
      simpa only [List.get_eq_getElem] using indexGet.trans freshGet.symm)
  subst index
  simp [ConcreteElaboration.extendedEnvironment,
    focusedFreshExtendedIndex, focusedFreshLocalIndex,
    focusedForwardLocal, Diagram.extendWireEnv, Function.comp_def]

theorem focusedForward_old_value
    (embedding : ContextEmbedding input payload source target)
    (sourceOuter : Fin source.length → D)
    (targetOuter : Fin target.length → D)
    (outerAgrees : sourceOuter = targetOuter ∘ embedding.index)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      payload.region).length → D)
    (fresh : Fin payload.argumentIndices.length → D)
    (targetNodup : (target.extend payload.region).Nodup)
    (wire : Fin input.val.wireCount)
    (targetIndex : Fin (target.extend payload.region).length)
    (targetGet : (target.extend payload.region).get targetIndex =
      Fin.castAdd payload.argumentIndices.length wire) :
    ∃ sourceIndex : Fin (source.extend payload.region).length,
      (source.extend payload.region).get sourceIndex = wire ∧
      ConcreteElaboration.extendedEnvironment target payload.region targetOuter
          (focusedForwardLocal input payload sourceLocal fresh) targetIndex =
        ConcreteElaboration.extendedEnvironment source payload.region
          sourceOuter sourceLocal sourceIndex := by
  have targetMember : Fin.castAdd payload.argumentIndices.length wire ∈
      target.extend payload.region := by
    rw [← targetGet]
    exact List.get_mem _ targetIndex
  have sourceMember : wire ∈ source.extend payload.region :=
    ((embedding.extend payload.region).mem_old wire).mp targetMember
  obtain ⟨sourceIndex, sourceLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceMember
  have sourceGet := ConcreteElaboration.WireContext.lookup?_sound sourceLookup
  have mappedGet := (embedding.extend payload.region).get sourceIndex
  have targetIndexEq : targetIndex =
      (embedding.extend payload.region).index sourceIndex := by
    apply Fin.ext
    exact (List.getElem_inj targetNodup).mp (by
      simpa only [List.get_eq_getElem] using targetGet.trans
        (mappedGet.trans (congrArg
          (Fin.castAdd payload.argumentIndices.length) sourceGet)).symm)
  refine ⟨sourceIndex, sourceGet, ?_⟩
  rw [targetIndexEq]
  exact congrFun (focusedForwardExtendedEnvironment embedding sourceOuter
    targetOuter outerAgrees sourceLocal fresh targetNodup).symm
      sourceIndex

private theorem compileNode_old_core
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (embedding : ContextEmbedding input payload source target)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (headStripExpandedRaw input payload) sourceBinders targetBinders)
    (targetNodup : target.Nodup)
    (node : Fin input.val.nodeCount) :
    ConcreteElaboration.compileNode? signature (headStripExpandedRaw input payload)
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
  · rw [headStripExpandedRaw_oldNode]
    cases input.val.nodes node <;> rfl
  · intro port
    apply ConcreteElaboration.resolvePort?_map_of_occurrence source target node
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) node)
      (Fin.castAdd payload.argumentIndices.length) embedding.index targetNodup
      embedding.get embedding.mem_old
    · intro wire candidatePort occurs
      exact headStripExpandedRaw_oldEndpointOccurs_forward input payload wire node
        candidatePort occurs
    · intro targetWire candidatePort occurs
      exact headStripExpandedRaw_oldEndpointOccurs_backward input payload targetWire node
        candidatePort occurs
    · exact targetWellFormed.wire_endpoints_are_disjoint
  · intro region binder nodeShape
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simp [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming]

theorem oldNodeOccurrences_simulation
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceRecurse : ∀ {relations : RelCtx},
      Fin input.val.regionCount →
      (recurseContext : ConcreteElaboration.WireContext input.val) →
      ConcreteElaboration.BinderContext input.val relations →
      Option (Region signature recurseContext.length relations))
    (targetRecurse : ∀ {relations : RelCtx},
      Fin (headStripExpandedRaw input payload).regionCount →
      (recurseContext : ConcreteElaboration.WireContext
        (headStripExpandedRaw input payload)) →
      ConcreteElaboration.BinderContext
        (headStripExpandedRaw input payload) relations →
      Option (Region signature recurseContext.length relations))
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (headStripExpandedRaw input payload))
    (embedding : ContextEmbedding input payload sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (headStripExpandedRaw input payload) sourceBinders targetBinders)
    (targetNodup : targetContext.Nodup)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val sourceRecurse sourceContext sourceBinders
      (sourceNodeOccurrences input payload.region) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (headStripExpandedRaw input payload) targetRecurse targetContext targetBinders
      ((sourceNodeOccurrences input payload.region).map
        (liftOccurrence payload)) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems := by
  apply ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model named direction sourceRecurse targetRecurse sourceContext targetContext
    sourceBinders targetBinders
    (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
    (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
    (liftOccurrence payload) (sourceNodeOccurrences input payload.region)
    ?_ sourceItems targetItems sourceCompiled targetCompiled
  intro occurrence member sourceItem targetItem sourceOccurrence targetOccurrence
  unfold sourceNodeOccurrences filterFin at member
  obtain ⟨node, nodeMember, rfl⟩ := List.mem_map.mp member
  simp only [ConcreteElaboration.compileOccurrenceWith?, liftOccurrence] at sourceOccurrence targetOccurrence
  have mappedCompile := compileNode_old_core input payload targetWellFormed
    sourceContext targetContext embedding sourceBinders targetBinders
    binderWitness targetNodup node
  rw [sourceOccurrence] at mappedCompile
  simp only [Option.map_some] at mappedCompile
  rw [targetOccurrence] at mappedCompile
  have itemEq : targetItem =
      (sourceItem.renameWires embedding.index).renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness) :=
    Option.some.inj mappedCompile
  subst targetItem
  intro sourceEnv targetEnv relEnv environments
  have environmentEq : sourceEnv = targetEnv ∘ embedding.index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceEnv targetEnv).mp environments
  rw [environmentEq]
  have wireSemantic := denoteItem_renameWires model named embedding.index
    targetEnv relEnv
    (sourceItem.renameRelations
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
  cases direction with
  | forward =>
      simpa only [Item.renameWires_renameRelations] using wireSemantic.mpr
  | backward =>
      simpa only [Item.renameWires_renameRelations] using wireSemantic.mp

theorem childOccurrence_simulation
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (headStripExpandedRaw input payload))
    (embedding : ContextEmbedding input payload sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (headStripExpandedRaw input payload) sourceBinders targetBinders)
    (sourceBindersCover : sourceBinders.Covers payload.region)
    (targetBindersCover : targetBinders.Covers payload.region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val sourceBinders payload.region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (headStripExpandedRaw input payload) targetBinders payload.region)
    (recurse : ∀ {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        input.val childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (headStripExpandedRaw input payload) childTargetRels}
      {sourceBody : Region signature sourceContext.length childSourceRels}
      {targetBody : Region signature targetContext.length childTargetRels},
      (input.val.regions child).parent? = some payload.region →
      ((headStripExpandedRaw input payload).regions child).parent? =
        some payload.region →
      True →
      (childBinderWitness : ConcreteElaboration.IdentityBinderWitness input.val
        (headStripExpandedRaw input payload) childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child →
      ConcreteElaboration.BinderContext.Enumeration input.val
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (headStripExpandedRaw input payload) childTargetBinders child →
      ConcreteElaboration.compileRegion? signature input.val fuelSource child
          sourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature (headStripExpandedRaw input payload)
          fuelTarget child targetContext childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
        (sourceBody.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            childBinderWitness)) targetBody)
    (child : Fin input.val.regionCount)
    (parent : (input.val.regions child).parent? = some payload.region)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) sourceContext sourceBinders (.child child) =
      some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (headStripExpandedRaw input payload)
      (ConcreteElaboration.compileRegion? signature
        (headStripExpandedRaw input payload) fuelTarget)
      targetContext targetBinders (.child child) = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      (sourceItem.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItem := by
  have targetParent : ((headStripExpandedRaw input payload).regions child).parent? =
      some payload.region := parent
  cases sourceKind : input.val.regions child with
  | sheet =>
      simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
        at sourceCompiled
  | cut actualParent =>
      have actualParentEq : actualParent = payload.region := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind : (headStripExpandedRaw input payload).regions child =
          .cut payload.region := by
        exact sourceKind
      cases sourceResult : ConcreteElaboration.compileRegion? signature
          input.val fuelSource child sourceContext sourceBinders with
      | none =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourceResult] at sourceCompiled
      | some sourceBody =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourceResult] at sourceCompiled
          subst sourceItem
          cases targetResult : ConcreteElaboration.compileRegion? signature
              (headStripExpandedRaw input payload) fuelTarget child targetContext
              targetBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetResult] at targetCompiled
          | some targetBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetResult] at targetCompiled
              subst targetItem
              have bodies := recurse (childDirection := direction.flip)
                parent targetParent True.intro
                binderWitness
                (ConcreteElaboration.BinderContext.covers_cut_child
                  sourceBindersCover sourceKind)
                (ConcreteElaboration.BinderContext.covers_cut_child
                  targetBindersCover targetKind)
                (sourceEnumeration.cutChild input.property sourceKind)
                (targetEnumeration.cutChild targetWellFormed targetKind)
                sourceResult targetResult
              intro sourceEnv targetEnv relEnv environments
              have bodyEntailment := bodies sourceEnv targetEnv relEnv
                environments
              simp only [Item.renameRelations, cut_denotes_negation]
              cases direction with
              | forward =>
                  exact fun sourceNot targetDenotes =>
                    sourceNot (bodyEntailment targetDenotes)
              | backward =>
                  exact fun targetNot sourceDenotes =>
                    targetNot (bodyEntailment sourceDenotes)
  | bubble actualParent arity =>
      have actualParentEq : actualParent = payload.region := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind : (headStripExpandedRaw input payload).regions child =
          .bubble payload.region arity := by
        exact sourceKind
      let sourcePushed := sourceBinders.push child arity
      let targetPushed := targetBinders.push child arity
      cases sourceResult : ConcreteElaboration.compileRegion? signature
          input.val fuelSource child sourceContext sourcePushed with
      | none =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourcePushed, sourceResult] at sourceCompiled
      | some sourceBody =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourcePushed, sourceResult] at sourceCompiled
          subst sourceItem
          cases targetResult : ConcreteElaboration.compileRegion? signature
              (headStripExpandedRaw input payload) fuelTarget child targetContext
              targetPushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetPushed, targetResult] at targetCompiled
          | some targetBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetPushed, targetResult] at targetCompiled
              subst targetItem
              let pushedWitness :
                  ConcreteElaboration.IdentityBinderWitness input.val
                    (headStripExpandedRaw input payload) sourcePushed targetPushed := by
                rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
                subst targetRels
                cases bindersEq
                exact ⟨rfl, HEq.rfl⟩
              have bodies := recurse (childDirection := direction)
                parent targetParent True.intro
                pushedWitness
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  sourceBindersCover sourceKind)
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  targetBindersCover targetKind)
                (sourceEnumeration.bubbleChild input.property sourceKind)
                (targetEnumeration.bubbleChild targetWellFormed targetKind)
                sourceResult targetResult
              have pushedMap :
                  (ConcreteElaboration.IdentityBinderWitness.relationMap
                    pushedWitness : RelationRenaming (arity :: sourceRels)
                      (arity :: targetRels)) =
                    (RelationRenaming.lift
                      (ConcreteElaboration.IdentityBinderWitness.relationMap
                        binderWitness) arity :
                      RelationRenaming (arity :: sourceRels)
                        (arity :: targetRels)) := by
                cases binderWitness.relationContexts_eq
                simpa [pushedWitness,
                  ConcreteElaboration.IdentityBinderWitness.relationMap,
                  ConcreteElaboration.identityRelationRenaming] using
                    (RelationRenaming.lift_id_fun
                      (source := sourceRels) arity).symm
              rw [pushedMap] at bodies
              intro sourceEnv targetEnv relEnv environments
              simp only [Item.renameRelations, bubble_denotes_exists]
              cases direction with
              | forward =>
                  rintro ⟨relationValue, sourceDenotes⟩
                  exact ⟨relationValue, bodies sourceEnv targetEnv
                    (relationValue, relEnv) environments sourceDenotes⟩
              | backward =>
                  rintro ⟨relationValue, targetDenotes⟩
                  exact ⟨relationValue, bodies sourceEnv targetEnv
                    (relationValue, relEnv) environments targetDenotes⟩

theorem childOccurrences_simulation
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceRecurse : ∀ {relations : RelCtx},
      Fin input.val.regionCount →
      (recurseContext : ConcreteElaboration.WireContext input.val) →
      ConcreteElaboration.BinderContext input.val relations →
      Option (Region signature recurseContext.length relations))
    (targetRecurse : ∀ {relations : RelCtx},
      Fin (headStripExpandedRaw input payload).regionCount →
      (recurseContext : ConcreteElaboration.WireContext
        (headStripExpandedRaw input payload)) →
      ConcreteElaboration.BinderContext
        (headStripExpandedRaw input payload) relations →
      Option (Region signature recurseContext.length relations))
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (headStripExpandedRaw input payload))
    (embedding : ContextEmbedding input payload sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (headStripExpandedRaw input payload) sourceBinders targetBinders)
    (pointwise : ∀ child,
      (input.val.regions child).parent? = some payload.region →
      ∀ (sourceItem : Item signature sourceContext.length sourceRels)
        (targetItem : Item signature targetContext.length targetRels),
      ConcreteElaboration.compileOccurrenceWith? signature input.val
          sourceRecurse sourceContext sourceBinders (.child child) =
        some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature
          (headStripExpandedRaw input payload) targetRecurse targetContext
          targetBinders (.child child) = some targetItem →
      ConcreteElaboration.ItemSimulation model named direction
        (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
        (sourceItem.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            binderWitness)) targetItem)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val sourceRecurse sourceContext sourceBinders
      (sourceChildOccurrences input payload.region) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (headStripExpandedRaw input payload) targetRecurse targetContext targetBinders
      ((sourceChildOccurrences input payload.region).map
        (liftOccurrence payload)) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems := by
  apply ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model named direction sourceRecurse targetRecurse sourceContext
    targetContext sourceBinders targetBinders
    (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
    (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
    (liftOccurrence payload) (sourceChildOccurrences input payload.region)
    ?_ sourceItems targetItems sourceCompiled targetCompiled
  intro occurrence member sourceItem targetItem sourceOccurrence
    targetOccurrence
  unfold sourceChildOccurrences filterFin at member
  obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
  have parent : (input.val.regions child).parent? = some payload.region := by
    exact of_decide_eq_true ((List.mem_filter.mp childMember).2)
  exact pointwise child parent sourceItem targetItem sourceOccurrence
    targetOccurrence

theorem compileNode_old
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext (headStripExpandedRaw input payload))
    (embedding : ContextEmbedding input payload source target)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (headStripExpandedRaw input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (headStripExpandedRaw input payload) sourceBinders targetBinders)
    (targetNodup : target.Nodup)
    (node : Fin input.val.nodeCount) :
    ConcreteElaboration.compileNode? signature (headStripExpandedRaw input payload)
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
  · rw [headStripExpandedRaw_oldNode]
    cases input.val.nodes node <;> rfl
  · intro port
    apply ConcreteElaboration.resolvePort?_map_of_occurrence source target node
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) node)
      (Fin.castAdd payload.argumentIndices.length) embedding.index targetNodup
      embedding.get embedding.mem_old
    · intro wire candidatePort occurs
      exact headStripExpandedRaw_oldEndpointOccurs_forward input payload wire node
        candidatePort occurs
    · intro targetWire candidatePort occurs
      exact headStripExpandedRaw_oldEndpointOccurs_backward input payload targetWire node
        candidatePort occurs
    · exact targetWellFormed.wire_endpoints_are_disjoint
  · intro region binder nodeShape
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simp [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming]

theorem source_common_environment
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext input.val)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (fuel : Nat)
    (items : ItemSeq signature context.length rels)
    (compiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        context binders
        (ConcreteElaboration.localOccurrences input.val payload.region) =
          some items)
    (exact : context.Exact payload.region)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels)
    (itemsDenote : denoteItemSeq Lambda.canonicalModel named env relEnv items) :
    ∃ common : Fin payload.commonPorts → Lambda.Individual,
      Lambda.canonicalModel.eval
          (payload.firstTerm.mapFree payload.firstPort) common =
        Lambda.canonicalModel.eval
          (payload.secondTerm.mapFree payload.secondPort) common ∧
      (∀ port index, context.get index = payload.firstWire port →
        env index = common (payload.firstPort port)) ∧
      (∀ port index, context.get index = payload.secondWire port →
        env index = common (payload.secondPort port)) := by
  obtain ⟨firstOutput, firstFree, firstOutputResult, firstFreeResult,
      firstEquation⟩ :=
    CongruenceSoundness.compiled_items_term_node_equation context binders fuel
      items compiled exact first payload.firstFreePorts payload.firstTerm
      payload.firstNode Lambda.canonicalModel named env relEnv itemsDenote
  obtain ⟨secondOutput, secondFree, secondOutputResult, secondFreeResult,
      secondEquation⟩ :=
    CongruenceSoundness.compiled_items_term_node_equation context binders fuel
      items compiled exact second payload.secondFreePorts payload.secondTerm
      payload.secondNode Lambda.canonicalModel named env relEnv itemsDenote
  obtain ⟨firstOwner, firstOwnerOccurs, firstOwnerGet⟩ :=
    ConcreteElaboration.resolvePort?_sound firstOutputResult
  obtain ⟨secondOwner, secondOwnerOccurs, secondOwnerGet⟩ :=
    ConcreteElaboration.resolvePort?_sound secondOutputResult
  have firstOwnerEq : firstOwner = payload.outputWire :=
    ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint firstOwnerOccurs
        payload.firstOutput
  have secondOwnerEq : secondOwner = payload.outputWire :=
    ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint secondOwnerOccurs
        payload.secondOutput
  have outputIndexEq : firstOutput = secondOutput := by
    apply Fin.ext
    exact (List.getElem_inj exact.nodup).mp (by
      simpa only [List.get_eq_getElem] using
        firstOwnerGet.trans (firstOwnerEq.trans
          (secondOwnerEq.symm.trans secondOwnerGet.symm)))
  have aligned : ∀ left right,
      payload.firstPort left = payload.secondPort right →
        (env ∘ firstFree) left = (env ∘ secondFree) right := by
    intro left right commonEq
    have firstResolved := sequenceFin_sound firstFreeResult left
    have secondResolved := sequenceFin_sound secondFreeResult right
    obtain ⟨firstWire, firstWireOccurs, firstWireGet⟩ :=
      ConcreteElaboration.resolvePort?_sound firstResolved
    obtain ⟨secondWire, secondWireOccurs, secondWireGet⟩ :=
      ConcreteElaboration.resolvePort?_sound secondResolved
    have firstWireEq : firstWire = payload.firstWire left :=
      ConcreteElaboration.endpoint_wire_unique
        input.property.wire_endpoints_are_disjoint firstWireOccurs
          (payload.firstWire_occurs left)
    have secondWireEq : secondWire = payload.secondWire right :=
      ConcreteElaboration.endpoint_wire_unique
        input.property.wire_endpoints_are_disjoint secondWireOccurs
          (payload.secondWire_occurs right)
    have indexEq : firstFree left = secondFree right := by
      apply Fin.ext
      exact (List.getElem_inj exact.nodup).mp (by
        simpa only [List.get_eq_getElem] using
          firstWireGet.trans (firstWireEq.trans
            ((payload.shared_wire left right commonEq).trans
              (secondWireEq.symm.trans secondWireGet.symm))))
    simp only [Function.comp_apply, indexEq]
  obtain ⟨common, firstCommon, secondCommon⟩ :=
    payload.exists_common_environment (env ∘ firstFree)
      (env ∘ secondFree) aligned
  refine ⟨common, ?_, ?_, ?_⟩
  · rw [Lambda.LambdaModel.eval_mapFree,
      Lambda.LambdaModel.eval_mapFree]
    exact (congrArg
      (fun environment =>
        Lambda.canonicalModel.eval payload.firstTerm environment)
      firstCommon).trans
        (firstEquation.symm.trans
          ((congrArg env outputIndexEq).trans
            (secondEquation.trans
              (congrArg
                (fun environment =>
                  Lambda.canonicalModel.eval payload.secondTerm environment)
                secondCommon.symm))))
  · intro port index indexGet
    have resolved := sequenceFin_sound firstFreeResult port
    obtain ⟨wire, occurs, wireGet⟩ :=
      ConcreteElaboration.resolvePort?_sound resolved
    have wireEq : wire = payload.firstWire port :=
      ConcreteElaboration.endpoint_wire_unique
        input.property.wire_endpoints_are_disjoint occurs
          (payload.firstWire_occurs port)
    have indexEq : index = firstFree port := by
      apply Fin.ext
      exact (List.getElem_inj exact.nodup).mp (by
        simpa only [List.get_eq_getElem] using
          indexGet.trans (wireEq.symm.trans wireGet.symm))
    rw [indexEq]
    exact (congrFun firstCommon port).symm
  · intro port index indexGet
    have resolved := sequenceFin_sound secondFreeResult port
    obtain ⟨wire, occurs, wireGet⟩ :=
      ConcreteElaboration.resolvePort?_sound resolved
    have wireEq : wire = payload.secondWire port :=
      ConcreteElaboration.endpoint_wire_unique
        input.property.wire_endpoints_are_disjoint occurs
          (payload.secondWire_occurs port)
    have indexEq : index = secondFree port := by
      apply Fin.ext
      exact (List.getElem_inj exact.nodup).mp (by
        simpa only [List.get_eq_getElem] using
          indexGet.trans (wireEq.symm.trans wireGet.symm))
    rw [indexEq]
    exact (congrFun secondCommon port).symm

def sourceOpen (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := input.val
  boundary := boundary

def targetOpen (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := headStripExpandedRaw input payload
  boundary := boundary.map (Fin.castAdd payload.argumentIndices.length)

theorem expectedTransport
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    (headStripExpandedInterfaceTransport input payload).transportBoundary boundary =
      some (boundary.map (Fin.castAdd payload.argumentIndices.length)) := by
  apply InterfaceTransport.transportBoundary_eq_map
  intro wire member
  unfold headStripExpandedInterfaceTransport InterfaceTransport.append
    InterfaceTransport.rootFiltered
  dsimp only
  have castEq :
      Fin.cast (show input.val.wireCount + payload.argumentIndices.length =
        (headStripExpandedRaw input payload).wireCount by rfl)
          (Fin.castAdd payload.argumentIndices.length wire) =
        Fin.castAdd payload.argumentIndices.length wire := by
    apply Fin.ext
    rfl
  rw [castEq]
  change (if ((headStripExpandedRaw input payload).wires
      (Fin.castAdd payload.argumentIndices.length wire)).scope =
        (headStripExpandedRaw input payload).root then
      some (Fin.castAdd payload.argumentIndices.length wire) else none) =
    some (Fin.castAdd payload.argumentIndices.length wire)
  rw [headStripExpandedRaw_oldWire_scope]
  simp [sourceRoot wire member]

def targetCheckedOpen
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed : (headStripExpandedRaw input payload).WellFormed signature) :
    CheckedOpenDiagram signature :=
  ⟨targetOpen input payload boundary, {
    diagram_well_formed := targetWellFormed
    boundary_is_root_scoped := by
      intro mapped member
      obtain ⟨wire, wireMember, rfl⟩ := List.mem_map.mp member
      exact headStripExpandedRaw_oldWire_scope input payload wire |>.trans
        (sourceRoot wire wireMember) }⟩

end HeadStripSoundness

end VisualProof.Rule
