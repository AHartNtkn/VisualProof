import VisualProof.Rule.Soundness.Equational.AnchoredWireContractInterface

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

private theorem finiteEquiv_fin_card_eq
    (equiv : FiniteEquiv (Fin left) (Fin right)) : left = right := by
  apply Nat.le_antisymm
  · exact fin_card_le_of_injective equiv equiv.injective
  · exact fin_card_le_of_injective equiv.symm equiv.symm.injective

/-- Reinsert the contracted closed node and its isolated output wire at the
original wire scope.  This is the exact pre-compaction carrier, up to the
stable survivor reindexing used by the executor. -/
def anchoredContractExpandedRaw
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount) : ConcreteDiagram :=
  spawnNodeRaw (anchoredWireContractRaw input redundant drop keep)
    (.term redundantRegion 0 redundantTerm) (input.val.wires drop).scope 1
    (fun _ => .output)

theorem anchoredContractExpandedRaw_regionCount
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount) :
    (anchoredContractExpandedRaw input redundant redundantRegion redundantTerm
      drop keep).regionCount = input.val.regionCount := rfl

theorem anchoredContractExpandedRaw_nodeCount
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount) :
    (anchoredContractExpandedRaw input redundant redundantRegion redundantTerm
      drop keep).nodeCount = input.val.nodeCount := by
  exact finiteEquiv_fin_card_eq (anchoredContractNodeRestore input redundant)

theorem anchoredContractExpandedRaw_wireCount
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount) :
    (anchoredContractExpandedRaw input redundant redundantRegion redundantTerm
      drop keep).wireCount = input.val.wireCount := by
  exact finiteEquiv_fin_card_eq (anchoredContractWireRestore input drop)

theorem anchoredContractExpandedRaw_node_restore
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (node : Fin (anchoredContractExpandedRaw input redundant redundantRegion
      redundantTerm drop keep).nodeCount)
    (shape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm) :
    ((anchoredContractExpandedRaw input redundant redundantRegion redundantTerm
      drop keep).nodes node).rename (.refl (Fin input.val.regionCount)) =
      input.val.nodes (anchoredContractNodeRestore input redundant node) := by
  refine Fin.lastCases ?_ (fun survivor => ?_) node
  · simp only [anchoredContractExpandedRaw, spawnNodeRaw_newNode,
      CNode.rename_refl]
    change CNode.term redundantRegion 0 redundantTerm =
      input.val.nodes
        (anchoredContractNodeRestore input redundant
          (Fin.last (anchoredContractNodeDomain input.val redundant).count))
    rw [anchoredContractNodeRestore, restoreDeletedEquiv_fresh]
    exact shape.symm
  · simp only [anchoredContractExpandedRaw, spawnNodeRaw_oldNode,
      CNode.rename_refl]
    change input.val.nodes
        ((anchoredContractNodeDomain input.val redundant).origin survivor) =
      input.val.nodes
        (anchoredContractNodeRestore input redundant survivor.castSucc)
    apply congrArg input.val.nodes
    exact (restoreDeletedEquiv_survivor
      (anchoredContractNodeDomain input.val redundant) redundant
      (by intro candidate; rfl) survivor).symm

def restoreContractedEndpoint
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (endpoint : CEndpoint
      (anchoredContractNodeDomain input.val redundant).count) :
    CEndpoint input.val.nodeCount :=
  { node := anchoredContractNodeRestore input redundant endpoint.node.castSucc
    port := endpoint.port }

@[simp] theorem restoreContractedEndpoint_eq
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (endpoint : CEndpoint
      (anchoredContractNodeDomain input.val redundant).count) :
    restoreContractedEndpoint input redundant endpoint =
      { node := (anchoredContractNodeDomain input.val redundant).origin
          endpoint.node
        port := endpoint.port } := by
  cases endpoint with
  | mk node port =>
      simp only [restoreContractedEndpoint, CEndpoint.rename]
      congr 1
      exact restoreDeletedEquiv_survivor
        (anchoredContractNodeDomain input.val redundant) redundant
        (by intro candidate; rfl) node

theorem filterMap_restoreContractedEndpoint
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (endpoints : List (CEndpoint input.val.nodeCount)) :
    (endpoints.filterMap
        (anchoredContractEndpoint?
          (anchoredContractNodeDomain input.val redundant))).map
        (restoreContractedEndpoint input redundant) =
      endpoints.filter fun endpoint => decide (endpoint.node ≠ redundant) := by
  induction endpoints with
  | nil => rfl
  | cons endpoint tail induction =>
      by_cases equality : endpoint.node = redundant
      · have hnone :
          (anchoredContractNodeDomain input.val redundant).index?
              endpoint.node = none := by
            rw [(anchoredContractNodeDomain input.val redundant
              ).index?_eq_none_iff]
            simp [anchoredContractNodeDomain, equality]
        have hhead : anchoredContractEndpoint?
            (anchoredContractNodeDomain input.val redundant) endpoint = none := by
          unfold anchoredContractEndpoint?
          rw [hnone]
          rfl
        rw [List.filterMap_cons, hhead]
        simp only [List.map_nil, List.nil_append]
        rw [List.filter_cons, if_neg (by simp [equality])]
        exact induction
      · have survives :
          (anchoredContractNodeDomain input.val redundant).survives
              endpoint.node = true := by
            simp [anchoredContractNodeDomain, equality]
        let compact := (anchoredContractNodeDomain input.val redundant).index
          endpoint.node survives
        have hsome :
            (anchoredContractNodeDomain input.val redundant).index?
              endpoint.node = some compact :=
          (anchoredContractNodeDomain input.val redundant).index?_index
            endpoint.node survives
        have horigin :
            (anchoredContractNodeDomain input.val redundant).origin compact =
              endpoint.node :=
          (anchoredContractNodeDomain input.val redundant).origin_index
            endpoint.node survives
        let compactEndpoint : CEndpoint
            (anchoredContractNodeDomain input.val redundant).count :=
          { node := compact, port := endpoint.port }
        have hhead : anchoredContractEndpoint?
            (anchoredContractNodeDomain input.val redundant) endpoint =
              some compactEndpoint := by
          unfold anchoredContractEndpoint?
          rw [hsome]
          rfl
        rw [List.filterMap_cons, hhead]
        simp only [List.map_cons]
        have hrestored : restoreContractedEndpoint input redundant
            compactEndpoint = endpoint := by
          cases endpoint with
          | mk node port =>
              simp only [compactEndpoint, restoreContractedEndpoint_eq]
              congr
        rw [hrestored, induction]
        simp [equality]

theorem endpoint_at_closed_redundant_eq_output
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (shape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (wire : Fin input.val.wireCount)
    (endpoint : CEndpoint input.val.nodeCount)
    (member : input.val.EndpointOccurs wire endpoint)
    (nodeEq : endpoint.node = redundant) :
    endpoint = { node := redundant, port := .output } := by
  have valid := input.property.endpoints_are_valid wire endpoint member
  rw [nodeEq] at valid
  rw [ConcreteDiagram.requiresPort_term_iff input.val redundant endpoint.port
    redundantRegion 0 redundantTerm shape] at valid
  rcases valid with output | free
  · cases endpoint
    simp only at nodeEq output
    subst nodeEq
    subst output
    rfl
  · obtain ⟨index, _⟩ := free
    exact Fin.elim0 index

theorem filterMap_restoreContractedEndpoint_of_wire_ne
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop wire : Fin input.val.wireCount)
    (shape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output })
    (wireNe : wire ≠ drop) :
    ((input.val.wires wire).endpoints.filterMap
        (anchoredContractEndpoint?
          (anchoredContractNodeDomain input.val redundant))).map
        (restoreContractedEndpoint input redundant) =
      (input.val.wires wire).endpoints := by
  rw [filterMap_restoreContractedEndpoint]
  apply List.filter_eq_self.mpr
  intro endpoint member
  apply decide_eq_true
  intro nodeEq
  have endpointEq := endpoint_at_closed_redundant_eq_output input redundant
    redundantRegion redundantTerm shape wire endpoint member nodeEq
  subst endpoint
  have disjoint := input.property.wire_endpoints_are_disjoint wire drop
    (by simpa only [bne_iff_ne] using wireNe)
    { node := redundant, port := .output } member
  rw [Bool.not_eq_true'] at disjoint
  exact (of_decide_eq_false disjoint) redundantOccurs

theorem filterMap_restoreContractedEndpoint_moved
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop : Fin input.val.wireCount) :
    input.val.nodes redundant = .term redundantRegion 0 redundantTerm →
    ((movedEndpoints input redundant drop).filterMap
        (anchoredContractEndpoint?
          (anchoredContractNodeDomain input.val redundant))).map
        (restoreContractedEndpoint input redundant) =
      movedEndpoints input redundant drop := by
  intro shape
  rw [filterMap_restoreContractedEndpoint]
  apply List.filter_eq_self.mpr
  intro endpoint member
  apply decide_eq_true
  intro nodeEq
  have endpointNe := movedEndpoints_ne_redundant input redundant drop member
  exact endpointNe (endpoint_at_closed_redundant_eq_output input redundant
    redundantRegion redundantTerm shape drop endpoint
      (movedEndpoints_mem_occurs input redundant drop member) nodeEq)

private theorem filter_eq_singleton_of_nodup
    [DecidableEq α]
    (values : List α) (witness : α)
    (nodup : values.Nodup) (member : witness ∈ values) :
    values.filter (fun value => decide (value = witness)) = [witness] := by
  induction values with
  | nil => contradiction
  | cons head tail induction =>
      have parts := List.nodup_cons.mp nodup
      by_cases equality : head = witness
      · subst head
        have none : tail.filter (fun value => decide (value = witness)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro value valueMem
          intro accepted
          have valueEq : value = witness := of_decide_eq_true accepted
          subst value
          exact parts.1 valueMem
        rw [List.filter_cons, if_pos (by simp), none]
      · have tailMember : witness ∈ tail := by
          rcases List.mem_cons.mp member with headEq | tailMember
          · exact False.elim (equality headEq.symm)
          · exact tailMember
        have tailResult := induction parts.2 tailMember
        rw [List.filter_cons, if_neg (by simp [equality]), tailResult]

theorem moveEndpointsRaw_drop_endpoints
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (drop keep : Fin input.val.wireCount)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output }) :
    ((moveEndpointsRaw input.val drop keep
      (movedEndpoints input redundant drop)).wires drop).endpoints =
        [{ node := redundant, port := .output }] := by
  simp only [moveEndpointsRaw, if_pos rfl]
  change ((input.val.wires drop).endpoints.filter fun current =>
    decide (current ∉ movedEndpoints input redundant drop)) = _
  have predicate : (input.val.wires drop).endpoints.filter (fun current =>
      decide (current ∉ movedEndpoints input redundant drop)) =
      (input.val.wires drop).endpoints.filter (fun current =>
        decide (current = { node := redundant, port := CPort.output })) := by
    apply List.filter_congr
    intro endpoint member
    apply Bool.eq_iff_iff.mpr
    simp [movedEndpoints, member]
  rw [predicate]
  exact filter_eq_singleton_of_nodup (input.val.wires drop).endpoints
    { node := redundant, port := .output }
    (input.property.endpoints_are_nodup drop) redundantOccurs

theorem anchoredContractExpandedRaw_oldWire_endpoints_restore
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (wire : Fin (anchoredWireContractRaw input redundant drop keep).wireCount) :
    ((anchoredContractExpandedRaw input redundant redundantRegion redundantTerm
      drop keep).wires wire.castSucc).endpoints.map
        (CEndpoint.rename (anchoredContractNodeRestore input redundant)) =
      ((anchoredWireContractRaw input redundant drop keep).wires wire).endpoints.map
        (restoreContractedEndpoint input redundant) := by
  have oldEq : wire.castSucc = Fin.castAdd 1 wire := rfl
  rw [oldEq]
  simp only [anchoredContractExpandedRaw, spawnNodeRaw, spawnLiftWire]
  rw [Fin.addCases_left]
  change List.map (CEndpoint.rename
      (anchoredContractNodeRestore input redundant))
      (List.map spawnLiftEndpoint
        ((anchoredWireContractRaw input redundant drop keep).wires wire
          ).endpoints) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro endpoint _
  cases endpoint
  rfl

/-- Stable compaction followed by reinsertion is the endpoint-batch graph,
up to the explicit survivor equivalences. -/
def anchoredContractExpandedIso
    (input : CheckedDiagram signature)
    (redundant : Fin input.val.nodeCount)
    (redundantRegion : Fin input.val.regionCount)
    (redundantTerm : Lambda.Term 0 (Fin 0))
    (drop keep : Fin input.val.wireCount)
    (shape : input.val.nodes redundant =
      .term redundantRegion 0 redundantTerm)
    (redundantOccurs : input.val.EndpointOccurs drop
      { node := redundant, port := .output }) :
    ConcreteIso
      (anchoredContractExpandedRaw input redundant redundantRegion redundantTerm
        drop keep)
      (moveEndpointsRaw input.val drop keep
        (movedEndpoints input redundant drop)) where
  regionCount_eq := rfl
  nodeCount_eq := anchoredContractExpandedRaw_nodeCount input redundant
    redundantRegion redundantTerm drop keep
  wireCount_eq := anchoredContractExpandedRaw_wireCount input redundant
    redundantRegion redundantTerm drop keep
  regions := .refl _
  nodes := anchoredContractNodeRestore input redundant
  wires := anchoredContractWireRestore input drop
  root_eq := rfl
  regions_eq := by
    intro region
    have sourceRegion :
        (anchoredContractExpandedRaw input redundant redundantRegion
          redundantTerm drop keep).regions region = input.val.regions region :=
      rfl
    have targetRegion :
        (moveEndpointsRaw input.val drop keep
          (movedEndpoints input redundant drop)).regions region =
            input.val.regions region := rfl
    rw [sourceRegion, FiniteEquiv.refl_apply, targetRegion]
    exact CRegion.rename_refl _
  nodes_eq := fun node => anchoredContractExpandedRaw_node_restore input
    redundant redundantRegion redundantTerm drop keep node shape
  wire_scope_eq := by
    intro wire
    refine Fin.lastCases ?_ (fun survivor => ?_) wire
    · simp only [anchoredContractExpandedRaw, FiniteEquiv.refl_apply]
      rw [show Fin.last
          (anchoredWireContractRaw input redundant drop keep).wireCount =
            Fin.natAdd
              (anchoredWireContractRaw input redundant drop keep).wireCount
              (0 : Fin 1) by rfl]
      rw [spawnNodeRaw_freshWire_scope]
      have freshEq :
          (Fin.natAdd
            (anchoredWireContractRaw input redundant drop keep).wireCount
            (0 : Fin 1)) =
          Fin.last (anchoredContractWireDomain input.val drop).count := rfl
      rw [freshEq, anchoredContractWireRestore, restoreDeletedEquiv_fresh]
      exact moveEndpointsRaw_wire_scope input.val drop keep
        drop (movedEndpoints input redundant drop) |>.symm
    · simp only [anchoredContractExpandedRaw, FiniteEquiv.refl_apply]
      have oldEq : survivor.castSucc = Fin.castAdd 1 survivor := rfl
      have sourceScope :
          ((spawnNodeRaw (anchoredWireContractRaw input redundant drop keep)
            (.term redundantRegion 0 redundantTerm)
            (input.val.wires drop).scope 1 (fun _ => .output)).wires
              survivor.castSucc).scope =
            ((anchoredWireContractRaw input redundant drop keep).wires
              survivor).scope := by
        rw [oldEq, spawnNodeRaw_oldWire_scope]
      rw [sourceScope]
      rw [moveEndpointsRaw_wire_scope input.val drop keep
        (anchoredContractWireRestore input drop survivor.castSucc)
        (movedEndpoints input redundant drop)]
      change (input.val.wires
          ((anchoredContractWireDomain input.val drop).origin survivor)).scope =
        (input.val.wires
          (anchoredContractWireRestore input drop survivor.castSucc)).scope
      apply congrArg (fun original => (input.val.wires original).scope)
      exact (restoreDeletedEquiv_survivor
        (anchoredContractWireDomain input.val drop) drop
        (by intro candidate; rfl) survivor).symm
  wire_endpoints_perm := by
    intro wire
    refine Fin.lastCases ?_ (fun survivor => ?_) wire
    · apply List.Perm.of_eq
      have freshEq : Fin.last
          (anchoredWireContractRaw input redundant drop keep).wireCount =
          Fin.natAdd
            (anchoredWireContractRaw input redundant drop keep).wireCount
            (0 : Fin 1) := rfl
      rw [freshEq]
      simp only [anchoredContractExpandedRaw]
      have sourceFresh :
          ((spawnNodeRaw (anchoredWireContractRaw input redundant drop keep)
            (.term redundantRegion 0 redundantTerm)
            (input.val.wires drop).scope 1 (fun _ => .output)).wires
              (Fin.natAdd
                (anchoredWireContractRaw input redundant drop keep).wireCount
                (0 : Fin 1))).endpoints =
            [{ node := Fin.last
                (anchoredWireContractRaw input redundant drop keep).nodeCount
              , port := .output }] := by
        simp [spawnNodeRaw]
      rw [sourceFresh]
      simp only [List.map_cons, List.map_nil]
      have nodeFresh : CEndpoint.rename
          (anchoredContractNodeRestore input redundant)
          { node := Fin.last
              (anchoredWireContractRaw input redundant drop keep).nodeCount
            , port := CPort.output } =
          { node := redundant, port := CPort.output } := by
        change (⟨anchoredContractNodeRestore input redundant
              (Fin.last
                (anchoredWireContractRaw input redundant drop keep).nodeCount),
            CPort.output⟩ : CEndpoint input.val.nodeCount) = _
        congr 1
        exact restoreDeletedEquiv_fresh
          (anchoredContractNodeDomain input.val redundant) redundant
          (by intro candidate; rfl)
      have wireFresh : anchoredContractWireRestore input drop
          (Fin.natAdd
            (anchoredWireContractRaw input redundant drop keep).wireCount
            (0 : Fin 1)) = drop := by
        exact restoreDeletedEquiv_fresh
          (anchoredContractWireDomain input.val drop) drop
          (by intro candidate; rfl)
      calc
        [CEndpoint.rename (anchoredContractNodeRestore input redundant)
            { node := Fin.last
                (anchoredWireContractRaw input redundant drop keep).nodeCount
              , port := CPort.output }] =
            [{ node := redundant, port := CPort.output }] :=
              congrArg (fun endpoint => [endpoint]) nodeFresh
        _ = ((moveEndpointsRaw input.val drop keep
              (movedEndpoints input redundant drop)).wires
                (anchoredContractWireRestore input drop
                  (Fin.natAdd
                    (anchoredWireContractRaw input redundant drop keep).wireCount
                    (0 : Fin 1)))).endpoints := by
              rw [wireFresh]
              exact moveEndpointsRaw_drop_endpoints input redundant drop keep
                redundantOccurs |>.symm
    · apply List.Perm.of_eq
      have sourceOld := anchoredContractExpandedRaw_oldWire_endpoints_restore
        input redundant redundantRegion redundantTerm drop keep survivor
      calc
        List.map (CEndpoint.rename (anchoredContractNodeRestore input redundant))
            ((anchoredContractExpandedRaw input redundant redundantRegion
              redundantTerm drop keep).wires survivor.castSucc).endpoints =
          List.map (restoreContractedEndpoint input redundant)
            ((anchoredWireContractRaw input redundant drop keep).wires
              survivor).endpoints := sourceOld
        _ = ((moveEndpointsRaw input.val drop keep
              (movedEndpoints input redundant drop)).wires
                (anchoredContractWireRestore input drop survivor.castSucc)
              ).endpoints := by
          let original :=
            (anchoredContractWireDomain input.val drop).origin survivor
          have survives :
              (anchoredContractWireDomain input.val drop).survives original =
                true :=
            (anchoredContractWireDomain input.val drop).origin_survives survivor
          have originalNe : original ≠ drop := by
            simpa [original, anchoredContractWireDomain] using survives
          have wireRestore : anchoredContractWireRestore input drop
              survivor.castSucc = original := by
            exact restoreDeletedEquiv_survivor
              (anchoredContractWireDomain input.val drop) drop
              (by intro candidate; rfl) survivor
          rw [wireRestore]
          by_cases keepEq : original = keep
          · have rawEndpoints :
                ((anchoredWireContractRaw input redundant drop keep).wires
                  survivor).endpoints =
                ((input.val.wires original).endpoints ++
                    movedEndpoints input redundant drop).filterMap
                  (anchoredContractEndpoint?
                    (anchoredContractNodeDomain input.val redundant)) := by
              change
                (if original = keep then
                    (input.val.wires original).endpoints ++
                      movedEndpoints input redundant drop
                  else (input.val.wires original).endpoints).filterMap
                    (anchoredContractEndpoint?
                      (anchoredContractNodeDomain input.val redundant)) = _
              rw [if_pos keepEq]
            rw [rawEndpoints, List.filterMap_append, List.map_append]
            rw [filterMap_restoreContractedEndpoint_of_wire_ne input redundant
              redundantRegion redundantTerm drop original shape redundantOccurs
              originalNe]
            rw [filterMap_restoreContractedEndpoint_moved input redundant
              redundantRegion redundantTerm drop shape]
            have keepNe : keep ≠ drop := by
              simpa [keepEq] using originalNe
            simp [moveEndpointsRaw, originalNe, keepEq, keepNe]
          · have rawEndpoints :
                ((anchoredWireContractRaw input redundant drop keep).wires
                  survivor).endpoints =
                (input.val.wires original).endpoints.filterMap
                  (anchoredContractEndpoint?
                    (anchoredContractNodeDomain input.val redundant)) := by
              change
                (if original = keep then
                    (input.val.wires original).endpoints ++
                      movedEndpoints input redundant drop
                  else (input.val.wires original).endpoints).filterMap
                    (anchoredContractEndpoint?
                      (anchoredContractNodeDomain input.val redundant)) = _
              rw [if_neg keepEq]
            rw [rawEndpoints]
            rw [filterMap_restoreContractedEndpoint_of_wire_ne input redundant
              redundantRegion redundantTerm drop original shape redundantOccurs
              originalNe]
            simp [moveEndpointsRaw, originalNe, keepEq]

end AnchoredWireContractSoundness

end VisualProof.Rule
