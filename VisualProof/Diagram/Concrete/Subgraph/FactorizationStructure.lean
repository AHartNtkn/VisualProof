import VisualProof.Diagram.Concrete.Subgraph.Factorization

namespace VisualProof

namespace RemovalFactorization

private theorem map_allFin_add
    (m n : Nat) (f : Fin (m + n) → α) :
    (Data.Finite.allFin (m + n)).map f =
      (Data.Finite.allFin m).map
          (fun index => f (Fin.castAdd n index)) ++
        (Data.Finite.allFin n).map
          (fun index => f (Fin.natAdd m index)) := by
  rw [Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn, List.map_ofFn, List.map_ofFn, List.ofFn_add]
  congr 1

private theorem allFin_add (m n : Nat) :
    Data.Finite.allFin (m + n) =
      (Data.Finite.allFin m).map (Fin.castAdd n) ++
        (Data.Finite.allFin n).map (Fin.natAdd m) := by
  have split := map_allFin_add m n (fun value => value)
  change
    (Data.Finite.allFin (m + n)).map id =
      (Data.Finite.allFin m).map (Fin.castAdd n) ++
        (Data.Finite.allFin n).map (Fin.natAdd m) at split
  simpa only [List.map_id] using split

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

private theorem hostRegion_injective
    (attachment : ConcreteSpliceAttachment removed fragment) :
    Function.Injective attachment.hostRegion := by
  intro left right same
  apply Fin.ext
  simpa [ConcreteSpliceAttachment.hostRegion] using
    congrArg Fin.val same

theorem fragmentRegion_eq_site_iff
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId) :
    attachment.fragmentRegion region =
        attachment.hostRegion removed.site ↔
      region = fragment.val.diagram.root := by
  constructor
  · intro same
    by_cases root : region = fragment.val.diagram.root
    · exact root
    · have impossible : False := by
        unfold ConcreteSpliceAttachment.fragmentRegion at same
        simp only [root, ↓reduceDIte] at same
        exact
          (attachment.hostRegion_ne_freshRegion removed.site _)
            same.symm
      exact impossible.elim
  · intro root
    subst region
    simp [ConcreteSpliceAttachment.fragmentRegion]

private theorem fragmentInternalWires_nodup
    (attachment : ConcreteSpliceAttachment removed fragment) :
    attachment.fragmentInternalWires.Nodup :=
  (Data.Finite.allFin_nodup fragment.val.diagram.wireCount).filter _

private theorem fragmentInternalWire_not_boundary
    (attachment : ConcreteSpliceAttachment removed fragment)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    attachment.fragmentInternalWires.get fresh ∉
      fragment.val.boundary := by
  have member :=
    List.get_mem attachment.fragmentInternalWires fresh
  simpa [ConcreteSpliceAttachment.fragmentInternalWires,
    ConcreteDiagram.wiresList] using
    (List.mem_filter.mp member).2

theorem fragmentWire_internal
    (attachment : ConcreteSpliceAttachment removed fragment)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    attachment.fragmentWire
        (attachment.fragmentInternalWires.get fresh) =
      attachment.freshWire fresh := by
  unfold ConcreteSpliceAttachment.fragmentWire
  simp only [fragmentInternalWire_not_boundary attachment fresh,
    ↓reduceDIte]
  congr 1
  exact DenseList.index_get attachment.fragmentInternalWires
    (fragmentInternalWires_nodup attachment) fresh

theorem candidate_wiresAt_site_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    attachment.diagram.wiresAt
        (attachment.hostRegion removed.site) =
      (ConcreteElaboration.openRootLocalWires fragment.val).map
        attachment.fragmentWire := by
  have hostFilter :
      (Data.Finite.allFin removed.complement.val.wireCount).filter
          (fun wire =>
            (attachment.diagram.wires
                (attachment.hostWire wire)).scope ==
              attachment.hostRegion removed.site) =
        removed.complement.val.wiresAt removed.site := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    apply List.filter_congr
    intro wire _
    simp only [
      ConcreteSpliceAttachment.diagram_wire_hostWire_scope]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro same
      exact hostRegion_injective attachment same
    · intro same
      exact congrArg attachment.hostRegion same
  have freshFilter :
      (Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (fun fresh =>
            (attachment.diagram.wires
                (attachment.freshWire fresh)).scope ==
              attachment.hostRegion removed.site) =
        (Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (fun fresh =>
            (fragment.val.diagram.wires
                (attachment.fragmentInternalWires.get fresh)).scope ==
              fragment.val.diagram.root) := by
    apply List.filter_congr
    intro fresh _
    simp only [
      ConcreteSpliceAttachment.diagram_wire_freshWire_scope]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact fragmentRegion_eq_site_iff attachment _
  have hostMapped :
      List.map (Fin.castAdd attachment.fragmentInternalWires.length)
        ((Data.Finite.allFin
          removed.complement.val.wireCount).filter
          (((fun wire =>
            (attachment.diagram.wires wire).scope ==
              attachment.hostRegion removed.site)) ∘
            Fin.castAdd attachment.fragmentInternalWires.length)) =
          [] := by
    have exactFilter :
        (Data.Finite.allFin
            removed.complement.val.wireCount).filter
            (((fun wire =>
              (attachment.diagram.wires wire).scope ==
                attachment.hostRegion removed.site)) ∘
              Fin.castAdd attachment.fragmentInternalWires.length) =
          removed.complement.val.wiresAt removed.site := by
      simpa only [Function.comp_apply,
        ConcreteSpliceAttachment.hostWire] using hostFilter
    have empty := complement_wiresAt_site_eq_nil occurrence
    change removed.complement.val.wiresAt removed.site = [] at empty
    exact congrArg
      (List.map (Fin.castAdd
        attachment.fragmentInternalWires.length))
      (exactFilter.trans empty)
  have freshMapped :
      List.map (Fin.natAdd removed.complement.val.wireCount)
        ((Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (((fun wire =>
            (attachment.diagram.wires wire).scope ==
              attachment.hostRegion removed.site)) ∘
            Fin.natAdd removed.complement.val.wireCount)) =
      ((Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (fun fresh =>
            (fragment.val.diagram.wires
                (attachment.fragmentInternalWires.get fresh)).scope ==
              fragment.val.diagram.root)).map attachment.freshWire := by
    have exactFilter :
        (Data.Finite.allFin
            attachment.fragmentInternalWires.length).filter
            (((fun wire =>
              (attachment.diagram.wires wire).scope ==
                attachment.hostRegion removed.site)) ∘
              Fin.natAdd removed.complement.val.wireCount) =
          (Data.Finite.allFin
            attachment.fragmentInternalWires.length).filter
            (fun fresh =>
              (fragment.val.diagram.wires
                  (attachment.fragmentInternalWires.get fresh)).scope ==
                fragment.val.diagram.root) := by
      simpa only [Function.comp_apply,
        ConcreteSpliceAttachment.freshWire] using freshFilter
    rw [exactFilter]
    rfl
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  change
    (Data.Finite.allFin
      (removed.complement.val.wireCount +
        attachment.fragmentInternalWires.length)).filter _ =
      _
  rw [allFin_add, List.filter_append, List.filter_map,
    List.filter_map]
  calc
    _ = [] ++
        ((Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (fun fresh =>
            (fragment.val.diagram.wires
                (attachment.fragmentInternalWires.get fresh)).scope ==
              fragment.val.diagram.root)).map attachment.freshWire :=
      (congrArg
          (fun left =>
            left ++
              List.map (Fin.natAdd
                removed.complement.val.wireCount)
                ((Data.Finite.allFin
                  attachment.fragmentInternalWires.length).filter
                  (((fun wire =>
                    (attachment.diagram.wires wire).scope ==
                      attachment.hostRegion removed.site)) ∘
                    Fin.natAdd
                      removed.complement.val.wireCount)))
          hostMapped).trans
        (congrArg (fun right => [] ++ right) freshMapped)
    _ = ((Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (fun fresh =>
            (fragment.val.diagram.wires
                (attachment.fragmentInternalWires.get fresh)).scope ==
              fragment.val.diagram.root)).map attachment.freshWire := by
      rfl
    _ = (ConcreteElaboration.openRootLocalWires fragment.val).map
          attachment.fragmentWire := by
      rw [show
          ((Data.Finite.allFin
            attachment.fragmentInternalWires.length).filter
            (fun fresh =>
              (fragment.val.diagram.wires
                  (attachment.fragmentInternalWires.get fresh)).scope ==
                fragment.val.diagram.root)).map attachment.freshWire =
            ((Data.Finite.allFin
              attachment.fragmentInternalWires.length).filter
              (fun fresh =>
                (fragment.val.diagram.wires
                    (attachment.fragmentInternalWires.get fresh)).scope ==
                  fragment.val.diagram.root)).map
                (fun fresh =>
                  attachment.fragmentWire
                    (attachment.fragmentInternalWires.get fresh)) by
          apply List.map_congr_left
          intro fresh _
          exact (fragmentWire_internal attachment fresh).symm]
      have sourceList :
          ((Data.Finite.allFin
            attachment.fragmentInternalWires.length).filter
            (fun fresh =>
              (fragment.val.diagram.wires
                  (attachment.fragmentInternalWires.get fresh)).scope ==
                fragment.val.diagram.root)).map
              attachment.fragmentInternalWires.get =
            ConcreteElaboration.openRootLocalWires fragment.val := by
        change
          List.map attachment.fragmentInternalWires.get
              (List.filter
                ((fun wire =>
                  (fragment.val.diagram.wires wire).scope ==
                    fragment.val.diagram.root) ∘
                  attachment.fragmentInternalWires.get)
                (Data.Finite.allFin
                  attachment.fragmentInternalWires.length)) =
            ConcreteElaboration.openRootLocalWires fragment.val
        rw [← List.filter_map, map_get_allFin]
        simp only [ConcreteElaboration.openRootLocalWires,
          ConcreteDiagram.wiresAt, ConcreteDiagram.wiresList,
          ConcreteSpliceAttachment.fragmentInternalWires,
          List.filter_filter]
        apply List.filter_congr
        intro wire _
        simp [ConcreteElaboration.openBoundaryWires,
          Bool.and_comm]
      simpa only [List.map_map, Function.comp_apply] using
        congrArg (List.map attachment.fragmentWire) sourceList

private theorem candidate_node_allocations
    (attachment : ConcreteSpliceAttachment removed fragment) :
    Data.Finite.allFin attachment.nodeCount =
      (Data.Finite.allFin
          removed.complement.val.nodeCount).map attachment.hostNode ++
        (Data.Finite.allFin
          fragment.val.diagram.nodeCount).map attachment.fragmentNode ++
        (Data.Finite.allFin
          attachment.identityRequests.length).map
            attachment.identityNode := by
  change
    Data.Finite.allFin
        (removed.complement.val.nodeCount +
          (fragment.val.diagram.nodeCount +
            attachment.identityRequests.length)) =
      _
  rw [allFin_add, allFin_add, List.map_append, List.map_map,
    List.map_map, List.append_assoc]
  have hostMap :
      (Data.Finite.allFin removed.complement.val.nodeCount).map
          (Fin.castAdd
            (fragment.val.diagram.nodeCount +
              attachment.identityRequests.length)) =
        (Data.Finite.allFin removed.complement.val.nodeCount).map
          attachment.hostNode := by
    rfl
  have fragmentMap :
      (Data.Finite.allFin fragment.val.diagram.nodeCount).map
          (Fin.natAdd removed.complement.val.nodeCount ∘
            Fin.castAdd attachment.identityRequests.length) =
        (Data.Finite.allFin fragment.val.diagram.nodeCount).map
          attachment.fragmentNode := by
    apply List.map_congr_left
    intro node _
    apply Fin.ext
    rfl
  have identityMap :
      (Data.Finite.allFin attachment.identityRequests.length).map
          (Fin.natAdd removed.complement.val.nodeCount ∘
            Fin.natAdd fragment.val.diagram.nodeCount) =
        (Data.Finite.allFin attachment.identityRequests.length).map
          attachment.identityNode := by
    apply List.map_congr_left
    intro identity _
    apply Fin.ext
    simp [ConcreteSpliceAttachment.identityNode]
    omega
  have tailMap :=
    (congrArg (fun values =>
      values ++
        (Data.Finite.allFin
          attachment.identityRequests.length).map
            (Fin.natAdd removed.complement.val.nodeCount ∘
              Fin.natAdd fragment.val.diagram.nodeCount))
      fragmentMap).trans
      (congrArg
        (List.append
          ((Data.Finite.allFin fragment.val.diagram.nodeCount).map
            attachment.fragmentNode))
        identityMap)
  exact
    (congrArg
      (fun values =>
        values ++
          ((Data.Finite.allFin
              fragment.val.diagram.nodeCount).map
              (Fin.natAdd removed.complement.val.nodeCount ∘
                Fin.castAdd attachment.identityRequests.length) ++
            (Data.Finite.allFin
              attachment.identityRequests.length).map
              (Fin.natAdd removed.complement.val.nodeCount ∘
                Fin.natAdd fragment.val.diagram.nodeCount)))
      hostMap).trans
      (congrArg
        (List.append
          ((Data.Finite.allFin
            removed.complement.val.nodeCount).map attachment.hostNode))
        tailMap)

theorem candidate_nodesAt_site_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    attachment.diagram.nodesAt
        (attachment.hostRegion removed.site) =
      (fragment.val.diagram.nodesAt fragment.val.diagram.root).map
          attachment.fragmentNode ++
        (Data.Finite.allFin
          attachment.identityRequests.length).map
            attachment.identityNode := by
  have hostFilter :
      (Data.Finite.allFin removed.complement.val.nodeCount).filter
          (fun node =>
            (attachment.diagram.nodes
                (attachment.hostNode node)).region ==
              attachment.hostRegion removed.site) =
        removed.complement.val.nodesAt removed.site := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.filter_congr
    intro node _
    simp only [
      ConcreteSpliceAttachment.diagram_node_hostNode_region]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro same
      exact hostRegion_injective attachment same
    · intro same
      exact congrArg attachment.hostRegion same
  have fragmentFilter :
      (Data.Finite.allFin fragment.val.diagram.nodeCount).filter
          (fun node =>
            (attachment.diagram.nodes
                (attachment.fragmentNode node)).region ==
              attachment.hostRegion removed.site) =
        fragment.val.diagram.nodesAt fragment.val.diagram.root := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.filter_congr
    intro node _
    simp only [
      ConcreteSpliceAttachment.diagram_node_fragmentNode_region]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact fragmentRegion_eq_site_iff attachment _
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change
    (Data.Finite.allFin attachment.nodeCount).filter _ = _
  rw [candidate_node_allocations, List.filter_append,
    List.filter_append, List.filter_map, List.filter_map,
    List.filter_map]
  have empty := complement_nodesAt_site_eq_nil occurrence
  change removed.complement.val.nodesAt removed.site = [] at empty
  have hostMapped :
      List.map attachment.hostNode
          ((Data.Finite.allFin
            removed.complement.val.nodeCount).filter
            (((fun node =>
              (attachment.diagram.nodes node).region ==
                attachment.hostRegion removed.site)) ∘
              attachment.hostNode)) =
        [] := by
    simpa only [Function.comp_apply, List.map_nil] using
      congrArg (List.map attachment.hostNode)
        (hostFilter.trans empty)
  have fragmentMapped :
      List.map attachment.fragmentNode
          ((Data.Finite.allFin
            fragment.val.diagram.nodeCount).filter
            (((fun node =>
              (attachment.diagram.nodes node).region ==
                attachment.hostRegion removed.site)) ∘
              attachment.fragmentNode)) =
        (fragment.val.diagram.nodesAt
          fragment.val.diagram.root).map attachment.fragmentNode := by
    simpa only [Function.comp_apply] using
      congrArg (List.map attachment.fragmentNode) fragmentFilter
  have identityFilter :
      (Data.Finite.allFin
          attachment.identityRequests.length).filter
          (((fun node =>
            (attachment.diagram.nodes node).region ==
              attachment.hostRegion removed.site)) ∘
            attachment.identityNode) =
        Data.Finite.allFin attachment.identityRequests.length := by
    apply List.filter_eq_self.mpr
    intro identity _
    simp [CNode.region]
  have identityMapped :
      List.map attachment.identityNode
          ((Data.Finite.allFin
            attachment.identityRequests.length).filter
            (((fun node =>
              (attachment.diagram.nodes node).region ==
                attachment.hostRegion removed.site)) ∘
              attachment.identityNode)) =
        (Data.Finite.allFin
          attachment.identityRequests.length).map
          attachment.identityNode :=
    congrArg (List.map attachment.identityNode) identityFilter
  calc
    _ = ([] ++
          List.map attachment.fragmentNode
            ((Data.Finite.allFin
              fragment.val.diagram.nodeCount).filter
              (((fun node =>
                (attachment.diagram.nodes node).region ==
                  attachment.hostRegion removed.site)) ∘
                attachment.fragmentNode))) ++
          List.map attachment.identityNode
            ((Data.Finite.allFin
              attachment.identityRequests.length).filter
              (((fun node =>
                (attachment.diagram.nodes node).region ==
                  attachment.hostRegion removed.site)) ∘
                attachment.identityNode)) := by
      exact congrArg
        (fun hostPart =>
          (hostPart ++
            List.map attachment.fragmentNode
              ((Data.Finite.allFin
                fragment.val.diagram.nodeCount).filter
                (((fun node =>
                  (attachment.diagram.nodes node).region ==
                    attachment.hostRegion removed.site)) ∘
                  attachment.fragmentNode))) ++
            List.map attachment.identityNode
              ((Data.Finite.allFin
                attachment.identityRequests.length).filter
                (((fun node =>
                  (attachment.diagram.nodes node).region ==
                    attachment.hostRegion removed.site)) ∘
                  attachment.identityNode)))
        hostMapped
    _ = ([] ++
          (fragment.val.diagram.nodesAt
            fragment.val.diagram.root).map attachment.fragmentNode) ++
          List.map attachment.identityNode
            ((Data.Finite.allFin
              attachment.identityRequests.length).filter
              (((fun node =>
                (attachment.diagram.nodes node).region ==
                  attachment.hostRegion removed.site)) ∘
                attachment.identityNode)) := by
      exact congrArg
        (fun fragmentPart =>
          ([] ++ fragmentPart) ++
            List.map attachment.identityNode
              ((Data.Finite.allFin
                attachment.identityRequests.length).filter
                (((fun node =>
                  (attachment.diagram.nodes node).region ==
                    attachment.hostRegion removed.site)) ∘
                  attachment.identityNode)))
        fragmentMapped
    _ = ([] ++
          (fragment.val.diagram.nodesAt
            fragment.val.diagram.root).map attachment.fragmentNode) ++
          (Data.Finite.allFin
            attachment.identityRequests.length).map
              attachment.identityNode := by
      exact congrArg
        (fun identityPart =>
          ([] ++
            (fragment.val.diagram.nodesAt
              fragment.val.diagram.root).map
                attachment.fragmentNode) ++ identityPart)
        identityMapped
    _ = _ := by rfl

private theorem fragmentRegions_nodup
    (attachment : ConcreteSpliceAttachment removed fragment) :
    attachment.fragmentRegions.Nodup :=
  (Data.Finite.allFin_nodup fragment.val.diagram.regionCount).filter _

private theorem fragmentRegion_nonroot
    (attachment : ConcreteSpliceAttachment removed fragment)
    (fresh : Fin attachment.fragmentRegions.length) :
    attachment.fragmentRegions.get fresh ≠ fragment.val.diagram.root := by
  have member := List.get_mem attachment.fragmentRegions fresh
  simpa [ConcreteSpliceAttachment.fragmentRegions,
    ConcreteDiagram.regionsList] using
    (List.mem_filter.mp member).2

theorem fragmentRegion_internal
    (attachment : ConcreteSpliceAttachment removed fragment)
    (fresh : Fin attachment.fragmentRegions.length) :
    attachment.fragmentRegion
        (attachment.fragmentRegions.get fresh) =
      attachment.freshRegion fresh := by
  unfold ConcreteSpliceAttachment.fragmentRegion
  simp only [fragmentRegion_nonroot attachment fresh,
    ↓reduceDIte]
  congr 1
  exact DenseList.index_get attachment.fragmentRegions
    (fragmentRegions_nodup attachment) fresh

private theorem candidate_region_allocations
    (attachment : ConcreteSpliceAttachment removed fragment) :
    Data.Finite.allFin attachment.regionCount =
      (Data.Finite.allFin
          removed.complement.val.regionCount).map
          attachment.hostRegion ++
        (Data.Finite.allFin
          attachment.fragmentRegions.length).map
            attachment.freshRegion := by
  change
    Data.Finite.allFin
        (removed.complement.val.regionCount +
          attachment.fragmentRegions.length) = _
  exact allFin_add _ _

theorem candidate_childrenOf_site_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    attachment.diagram.childrenOf
        (attachment.hostRegion removed.site) =
      (fragment.val.diagram.childrenOf
        fragment.val.diagram.root).map attachment.fragmentRegion := by
  let candidateIsChild :
      attachment.diagram.RegionId → Bool :=
    fun child =>
      match attachment.diagram.regions child with
      | .sheet => false
      | .cut parent =>
          parent == attachment.hostRegion removed.site
  let fragmentIsChild :
      fragment.val.diagram.RegionId → Bool :=
    fun child =>
      match fragment.val.diagram.regions child with
      | .sheet => false
      | .cut parent =>
          parent == fragment.val.diagram.root
  have candidateChildren :
      attachment.diagram.childrenOf
          (attachment.hostRegion removed.site) =
        attachment.diagram.regionsList.filter
          candidateIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold candidateIsChild
    cases attachment.diagram.regions child <;> rfl
  have fragmentChildren :
      fragment.val.diagram.childrenOf
          fragment.val.diagram.root =
        fragment.val.diagram.regionsList.filter
          fragmentIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold fragmentIsChild
    cases fragment.val.diagram.regions child <;> rfl
  rw [candidateChildren, fragmentChildren]
  have hostFilter :
      (Data.Finite.allFin
          removed.complement.val.regionCount).filter
          (candidateIsChild ∘ attachment.hostRegion) =
        removed.complement.val.childrenOf removed.site := by
    unfold candidateIsChild
    unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
    apply List.filter_congr
    intro child _
    simp only [Function.comp_apply]
    cases data : removed.complement.val.regions child with
    | sheet =>
        simp [data, mapRegion]
    | cut parent =>
        simp only [
          ConcreteSpliceAttachment.diagram_region_hostRegion,
          data, mapRegion]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        constructor
        · intro same
          exact hostRegion_injective attachment same
        · intro same
          exact congrArg attachment.hostRegion same
  have freshFilter :
      (Data.Finite.allFin
          attachment.fragmentRegions.length).filter
          (candidateIsChild ∘ attachment.freshRegion) =
        (Data.Finite.allFin
          attachment.fragmentRegions.length).filter
          (fragmentIsChild ∘
            attachment.fragmentRegions.get) := by
    unfold candidateIsChild fragmentIsChild
    apply List.filter_congr
    intro fresh _
    simp only [Function.comp_apply]
    cases data :
        fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh) with
    | sheet =>
        rw [
          ConcreteSpliceAttachment.diagram_region_freshRegion,
          data]
        rfl
    | cut parent =>
        rw [
          ConcreteSpliceAttachment.diagram_region_freshRegion,
          data]
        simp only [mapRegion]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact fragmentRegion_eq_site_iff attachment parent
  have allocations :
      attachment.diagram.regionsList =
        (Data.Finite.allFin
            removed.complement.val.regionCount).map
            attachment.hostRegion ++
          (Data.Finite.allFin
            attachment.fragmentRegions.length).map
              attachment.freshRegion := by
    unfold ConcreteDiagram.regionsList
    simpa only [ConcreteSpliceAttachment.diagram] using
      candidate_region_allocations attachment
  have allocatedFilter :=
    congrArg (List.filter candidateIsChild) allocations
  have expandedFilter :
      attachment.diagram.regionsList.filter candidateIsChild =
        List.map attachment.hostRegion
            ((Data.Finite.allFin
              removed.complement.val.regionCount).filter
              (candidateIsChild ∘
                attachment.hostRegion)) ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
              (candidateIsChild ∘
                attachment.freshRegion)) := by
    refine allocatedFilter.trans ?_
    calc
      List.filter _
          (List.map attachment.hostRegion
              (Data.Finite.allFin
                removed.complement.val.regionCount) ++
            List.map attachment.freshRegion
              (Data.Finite.allFin
                attachment.fragmentRegions.length)) =
          List.filter _
              (List.map attachment.hostRegion
                (Data.Finite.allFin
                  removed.complement.val.regionCount)) ++
            List.filter _
              (List.map attachment.freshRegion
                (Data.Finite.allFin
                  attachment.fragmentRegions.length)) :=
        List.filter_append _ _
      _ =
          List.map attachment.hostRegion
              ((Data.Finite.allFin
                removed.complement.val.regionCount).filter
                (_ ∘ attachment.hostRegion)) ++
            List.filter _
              (List.map attachment.freshRegion
                (Data.Finite.allFin
                  attachment.fragmentRegions.length)) :=
        congrArg
          (fun hostPart =>
            hostPart ++
              List.filter _
                (List.map attachment.freshRegion
                  (Data.Finite.allFin
                    attachment.fragmentRegions.length)))
          List.filter_map
      _ = _ :=
        congrArg
          (fun freshPart =>
            List.map attachment.hostRegion
                ((Data.Finite.allFin
                  removed.complement.val.regionCount).filter
                  (_ ∘ attachment.hostRegion)) ++
              freshPart)
          List.filter_map
  have empty := complement_childrenOf_site_eq_nil occurrence
  change removed.complement.val.childrenOf removed.site = [] at empty
  have hostMapped :
      List.map attachment.hostRegion
          ((Data.Finite.allFin
            removed.complement.val.regionCount).filter
            (candidateIsChild ∘
              attachment.hostRegion)) =
        [] := by
    simpa only [List.map_nil] using
      congrArg (List.map attachment.hostRegion)
        (hostFilter.trans empty)
  have freshMapped :
      List.map attachment.freshRegion
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (candidateIsChild ∘
              attachment.freshRegion)) =
        List.map attachment.freshRegion
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (fragmentIsChild ∘
              attachment.fragmentRegions.get)) := by
    exact congrArg (List.map attachment.freshRegion) freshFilter
  have hostEliminated :
      List.map attachment.hostRegion
            ((Data.Finite.allFin
              removed.complement.val.regionCount).filter
              (candidateIsChild ∘
                attachment.hostRegion)) ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (candidateIsChild ∘
                attachment.freshRegion)) =
        List.map attachment.freshRegion
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (candidateIsChild ∘
              attachment.freshRegion)) := by
    simpa only [List.nil_append] using
      congrArg
        (fun hostPart =>
          hostPart ++
            List.map attachment.freshRegion
              ((Data.Finite.allFin
                attachment.fragmentRegions.length).filter
                (candidateIsChild ∘
                  attachment.freshRegion)))
        hostMapped
  have sourceList :
      List.map attachment.fragmentRegions.get
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (fragmentIsChild ∘
              attachment.fragmentRegions.get)) =
        fragment.val.diagram.regionsList.filter
          fragmentIsChild := by
    rw [← List.filter_map, map_get_allFin]
    unfold ConcreteSpliceAttachment.fragmentRegions
    rw [List.filter_filter]
    apply List.filter_congr
    intro region _
    by_cases root : region = fragment.val.diagram.root
    · subst region
      unfold fragmentIsChild
      rw [fragment.property.diagram.root_is_sheet]
      rfl
    · have decided :
          decide (region ≠ fragment.val.diagram.root) = true :=
        decide_eq_true root
      rw [decided]
      unfold fragmentIsChild
      cases fragment.val.diagram.regions region <;>
        simp only [Bool.and_true]
  have candidateSources :
      List.map attachment.fragmentRegions.get
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (candidateIsChild ∘
              attachment.freshRegion)) =
        fragment.val.diagram.regionsList.filter
          fragmentIsChild := by
    exact
      (congrArg (List.map attachment.fragmentRegions.get)
        freshFilter).trans sourceList
  have freshAsFragment :
      List.map attachment.freshRegion
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (candidateIsChild ∘
              attachment.freshRegion)) =
        List.map
          (fun fresh =>
            attachment.fragmentRegion
              (attachment.fragmentRegions.get fresh))
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (candidateIsChild ∘
              attachment.freshRegion)) := by
    apply List.map_congr_left
    intro fresh _
    exact (fragmentRegion_internal attachment fresh).symm
  have mappedSources :
      List.map
          (fun fresh =>
            attachment.fragmentRegion
              (attachment.fragmentRegions.get fresh))
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (candidateIsChild ∘
              attachment.freshRegion)) =
        (fragment.val.diagram.regionsList.filter
          fragmentIsChild).map attachment.fragmentRegion := by
    simpa only [List.map_map, Function.comp_apply] using
      congrArg (List.map attachment.fragmentRegion) candidateSources
  have chain :=
    hostEliminated.trans
      (freshAsFragment.trans mappedSources)
  exact expandedFilter.trans chain

private theorem fragmentRegion_injective
    (attachment : ConcreteSpliceAttachment removed fragment) :
    Function.Injective attachment.fragmentRegion := by
  intro left right same
  by_cases leftRoot : left = fragment.val.diagram.root
  · subst left
    have rightRoot :=
      (fragmentRegion_eq_site_iff attachment right).mp (by
        simpa [ConcreteSpliceAttachment.fragmentRegion] using same.symm)
    exact rightRoot.symm
  · by_cases rightRoot : right = fragment.val.diagram.root
    · subst right
      have leftAtRoot :=
        (fragmentRegion_eq_site_iff attachment left).mp (by
          simpa [ConcreteSpliceAttachment.fragmentRegion] using same)
      exact (leftRoot leftAtRoot).elim
    · unfold ConcreteSpliceAttachment.fragmentRegion at same
      simp only [leftRoot, rightRoot, ↓reduceDIte] at same
      have indices :
          DenseList.index attachment.fragmentRegions left (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, leftRoot]) =
            DenseList.index attachment.fragmentRegions right (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, rightRoot]) := by
        apply Fin.ext
        simpa [ConcreteSpliceAttachment.freshRegion] using
          congrArg Fin.val same
      calc
        left = attachment.fragmentRegions.get
            (DenseList.index attachment.fragmentRegions left (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, leftRoot])) :=
          (DenseList.get_index _ _ _).symm
        _ = attachment.fragmentRegions.get
            (DenseList.index attachment.fragmentRegions right (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, rightRoot])) :=
          congrArg attachment.fragmentRegions.get indices
        _ = right := DenseList.get_index _ _ _

theorem candidate_nodesAt_fragmentRegion_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    attachment.diagram.nodesAt (attachment.fragmentRegion region) =
      (fragment.val.diagram.nodesAt region).map
        attachment.fragmentNode := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change
    (Data.Finite.allFin attachment.nodeCount).filter _ = _
  rw [candidate_node_allocations, List.filter_append,
    List.filter_append, List.filter_map, List.filter_map,
    List.filter_map]
  have hostEmpty :
      (Data.Finite.allFin removed.complement.val.nodeCount).filter
          (((fun node =>
            (attachment.diagram.nodes node).region ==
              attachment.fragmentRegion region) ∘
            attachment.hostNode)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro node member
    have accepted := (List.mem_filter.mp member).2
    simp only [Function.comp_apply,
      ConcreteSpliceAttachment.diagram_node_hostNode_region,
      beq_iff_eq] at accepted
    unfold ConcreteSpliceAttachment.fragmentRegion at accepted
    simp only [nonroot, ↓reduceDIte] at accepted
    exact attachment.hostRegion_ne_freshRegion _ _ accepted
  have fragmentFilter :
      (Data.Finite.allFin fragment.val.diagram.nodeCount).filter
          (((fun node =>
            (attachment.diagram.nodes node).region ==
              attachment.fragmentRegion region) ∘
            attachment.fragmentNode)) =
        fragment.val.diagram.nodesAt region := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.filter_congr
    intro node _
    simp only [Function.comp_apply,
      ConcreteSpliceAttachment.diagram_node_fragmentNode_region]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨fun same => fragmentRegion_injective attachment same,
      fun same => congrArg attachment.fragmentRegion same⟩
  have identitiesEmpty :
      (Data.Finite.allFin attachment.identityRequests.length).filter
          (((fun node =>
            (attachment.diagram.nodes node).region ==
              attachment.fragmentRegion region) ∘
            attachment.identityNode)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro identity member
    have accepted := (List.mem_filter.mp member).2
    simp only [Function.comp_apply,
      ConcreteSpliceAttachment.diagram_node_identityNode,
      CNode.region, beq_iff_eq] at accepted
    unfold ConcreteSpliceAttachment.fragmentRegion at accepted
    simp only [nonroot, ↓reduceDIte] at accepted
    exact attachment.hostRegion_ne_freshRegion _ _ accepted
  let hostPart :=
    List.map attachment.hostNode
      ((Data.Finite.allFin
        removed.complement.val.nodeCount).filter
        (((fun node =>
          (attachment.diagram.nodes node).region ==
            attachment.fragmentRegion region) ∘
          attachment.hostNode)))
  let fragmentPart :=
    List.map attachment.fragmentNode
      ((Data.Finite.allFin
        fragment.val.diagram.nodeCount).filter
        (((fun node =>
          (attachment.diagram.nodes node).region ==
            attachment.fragmentRegion region) ∘
          attachment.fragmentNode)))
  let identityPart :=
    List.map attachment.identityNode
      ((Data.Finite.allFin
        attachment.identityRequests.length).filter
        (((fun node =>
          (attachment.diagram.nodes node).region ==
            attachment.fragmentRegion region) ∘
          attachment.identityNode)))
  let sourcePart :=
    List.map attachment.fragmentNode
      (fragment.val.diagram.nodesAt region)
  change hostPart ++ fragmentPart ++ identityPart = sourcePart
  have hostPartEmpty : hostPart = [] :=
    congrArg (List.map attachment.hostNode) hostEmpty
  have fragmentPartExact : fragmentPart = sourcePart :=
    congrArg (List.map attachment.fragmentNode) fragmentFilter
  have identityPartEmpty : identityPart = [] :=
    congrArg (List.map attachment.identityNode) identitiesEmpty
  rw [hostPartEmpty, fragmentPartExact, identityPartEmpty]
  exact List.append_nil sourcePart

private theorem candidate_wire_allocations
    (attachment : ConcreteSpliceAttachment removed fragment) :
    Data.Finite.allFin attachment.wireCount =
      (Data.Finite.allFin
          removed.complement.val.wireCount).map attachment.hostWire ++
        (Data.Finite.allFin
          attachment.fragmentInternalWires.length).map
            attachment.freshWire := by
  change
    Data.Finite.allFin
        (removed.complement.val.wireCount +
          attachment.fragmentInternalWires.length) = _
  exact allFin_add _ _

private theorem boundaryWire_scope_eq_root
    (fragment : CheckedOpenDiagram definitions)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    (fragment.val.diagram.wires wire).scope =
      fragment.val.diagram.root := by
  have checked :=
    (List.all_eq_true.mp fragment.property.boundary_root_scoped)
      wire member
  exact of_decide_eq_true checked

theorem candidate_wiresAt_fragmentRegion_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    attachment.diagram.wiresAt (attachment.fragmentRegion region) =
      (fragment.val.diagram.wiresAt region).map
        attachment.fragmentWire := by
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  change
    (Data.Finite.allFin attachment.wireCount).filter _ = _
  rw [candidate_wire_allocations, List.filter_append,
    List.filter_map, List.filter_map]
  have hostEmpty :
      (Data.Finite.allFin removed.complement.val.wireCount).filter
          (((fun wire =>
            (attachment.diagram.wires wire).scope ==
              attachment.fragmentRegion region) ∘
            attachment.hostWire)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro wire member
    have accepted := (List.mem_filter.mp member).2
    simp only [Function.comp_apply,
      ConcreteSpliceAttachment.diagram_wire_hostWire_scope,
      beq_iff_eq] at accepted
    unfold ConcreteSpliceAttachment.fragmentRegion at accepted
    simp only [nonroot, ↓reduceDIte] at accepted
    exact attachment.hostRegion_ne_freshRegion _ _ accepted
  have freshFilter :
      (Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (((fun wire =>
            (attachment.diagram.wires wire).scope ==
              attachment.fragmentRegion region) ∘
            attachment.freshWire)) =
        (Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (fun fresh =>
            (fragment.val.diagram.wires
              (attachment.fragmentInternalWires.get fresh)).scope ==
                region) := by
    apply List.filter_congr
    intro fresh _
    simp only [Function.comp_apply,
      ConcreteSpliceAttachment.diagram_wire_freshWire_scope]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨fun same => fragmentRegion_injective attachment same,
      fun same => congrArg attachment.fragmentRegion same⟩
  have sourceList :
      List.map attachment.fragmentInternalWires.get
          ((Data.Finite.allFin
            attachment.fragmentInternalWires.length).filter
            (fun fresh =>
              (fragment.val.diagram.wires
                (attachment.fragmentInternalWires.get fresh)).scope ==
                  region)) =
        fragment.val.diagram.wiresAt region := by
    change
      List.map attachment.fragmentInternalWires.get
          (List.filter
            ((fun wire =>
              (fragment.val.diagram.wires wire).scope == region) ∘
              attachment.fragmentInternalWires.get)
            (Data.Finite.allFin
              attachment.fragmentInternalWires.length)) =
        fragment.val.diagram.wiresAt region
    rw [← List.filter_map, map_get_allFin]
    unfold ConcreteSpliceAttachment.fragmentInternalWires
      ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    rw [List.filter_filter]
    apply List.filter_congr
    intro wire _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true]
    constructor
    · exact fun accepted => accepted.1
    · intro atRegion
      refine ⟨atRegion, decide_eq_true ?_⟩
      intro boundary
      have rootScope := boundaryWire_scope_eq_root fragment wire boundary
      have regionScope := eq_of_beq atRegion
      exact nonroot (rootScope.symm.trans regionScope).symm
  let hostPart :=
    List.map attachment.hostWire
      ((Data.Finite.allFin
        removed.complement.val.wireCount).filter
        (((fun wire =>
          (attachment.diagram.wires wire).scope ==
            attachment.fragmentRegion region) ∘
          attachment.hostWire)))
  let freshPart :=
    List.map attachment.freshWire
      ((Data.Finite.allFin
        attachment.fragmentInternalWires.length).filter
        (((fun wire =>
          (attachment.diagram.wires wire).scope ==
            attachment.fragmentRegion region) ∘
          attachment.freshWire)))
  let sourcePart :=
    (fragment.val.diagram.wiresAt region).map
      attachment.fragmentWire
  change hostPart ++ freshPart = sourcePart
  have hostPartEmpty : hostPart = [] :=
    congrArg (List.map attachment.hostWire) hostEmpty
  have freshPartExact : freshPart = sourcePart := by
    dsimp only [freshPart, sourcePart]
    rw [freshFilter]
    calc
      _ = List.map
            (fun fresh =>
              attachment.fragmentWire
                (attachment.fragmentInternalWires.get fresh))
            ((Data.Finite.allFin
              attachment.fragmentInternalWires.length).filter
              (fun fresh =>
                (fragment.val.diagram.wires
                  (attachment.fragmentInternalWires.get fresh)).scope ==
                    region)) := by
          apply List.map_congr_left
          intro fresh _
          exact (fragmentWire_internal attachment fresh).symm
      _ = _ := by
        simpa only [List.map_map, Function.comp_apply] using
          congrArg (List.map attachment.fragmentWire) sourceList
  rw [hostPartEmpty, freshPartExact]
  rfl

theorem candidate_childrenOf_fragmentRegion_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    attachment.diagram.childrenOf
        (attachment.fragmentRegion region) =
      (fragment.val.diagram.childrenOf region).map
        attachment.fragmentRegion := by
  let candidateIsChild :
      attachment.diagram.RegionId → Bool :=
    fun child =>
      match attachment.diagram.regions child with
      | .sheet => false
      | .cut parent =>
          parent == attachment.fragmentRegion region
  let fragmentIsChild :
      fragment.val.diagram.RegionId → Bool :=
    fun child =>
      match fragment.val.diagram.regions child with
      | .sheet => false
      | .cut parent => parent == region
  have candidateChildren :
      attachment.diagram.childrenOf
          (attachment.fragmentRegion region) =
        attachment.diagram.regionsList.filter
          candidateIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold candidateIsChild
    cases attachment.diagram.regions child <;> rfl
  have fragmentChildren :
      fragment.val.diagram.childrenOf region =
        fragment.val.diagram.regionsList.filter
          fragmentIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold fragmentIsChild
    cases fragment.val.diagram.regions child <;> rfl
  rw [candidateChildren, fragmentChildren]
  have allocations :
      attachment.diagram.regionsList =
        (Data.Finite.allFin
            removed.complement.val.regionCount).map
            attachment.hostRegion ++
          (Data.Finite.allFin
            attachment.fragmentRegions.length).map
              attachment.freshRegion := by
    unfold ConcreteDiagram.regionsList
    simpa only [ConcreteSpliceAttachment.diagram] using
      candidate_region_allocations attachment
  have allocatedFilter :=
    congrArg (List.filter candidateIsChild) allocations
  have expanded :
      attachment.diagram.regionsList.filter candidateIsChild =
        List.map attachment.hostRegion
            ((Data.Finite.allFin
              removed.complement.val.regionCount).filter
              (candidateIsChild ∘ attachment.hostRegion)) ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (candidateIsChild ∘ attachment.freshRegion)) := by
    refine allocatedFilter.trans ?_
    calc
      List.filter _
          (List.map attachment.hostRegion
              (Data.Finite.allFin
                removed.complement.val.regionCount) ++
            List.map attachment.freshRegion
              (Data.Finite.allFin
                attachment.fragmentRegions.length)) =
          List.filter _
              (List.map attachment.hostRegion
                (Data.Finite.allFin
                  removed.complement.val.regionCount)) ++
            List.filter _
              (List.map attachment.freshRegion
                (Data.Finite.allFin
                  attachment.fragmentRegions.length)) :=
        List.filter_append _ _
      _ =
          List.map attachment.hostRegion
              ((Data.Finite.allFin
                removed.complement.val.regionCount).filter
                (_ ∘ attachment.hostRegion)) ++
            List.filter _
              (List.map attachment.freshRegion
                (Data.Finite.allFin
                  attachment.fragmentRegions.length)) :=
        congrArg
          (fun hostPart =>
            hostPart ++
              List.filter _
                (List.map attachment.freshRegion
                  (Data.Finite.allFin
                    attachment.fragmentRegions.length)))
          List.filter_map
      _ = _ :=
        congrArg
          (fun freshPart =>
            List.map attachment.hostRegion
                ((Data.Finite.allFin
                  removed.complement.val.regionCount).filter
                  (_ ∘ attachment.hostRegion)) ++
              freshPart)
          List.filter_map
  rw [expanded]
  have hostEmpty :
      (Data.Finite.allFin
        removed.complement.val.regionCount).filter
        (candidateIsChild ∘ attachment.hostRegion) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro child member
    have accepted := (List.mem_filter.mp member).2
    unfold candidateIsChild at accepted
    simp only [Function.comp_apply] at accepted
    cases data : removed.complement.val.regions child with
    | sheet =>
        simp [ConcreteSpliceAttachment.diagram_region_hostRegion,
          data, mapRegion] at accepted
    | cut parent =>
        simp only [
          ConcreteSpliceAttachment.diagram_region_hostRegion,
          data, mapRegion, beq_iff_eq] at accepted
        unfold ConcreteSpliceAttachment.fragmentRegion at accepted
        simp only [nonroot, ↓reduceDIte] at accepted
        exact attachment.hostRegion_ne_freshRegion _ _ accepted
  have freshFilter :
      (Data.Finite.allFin
        attachment.fragmentRegions.length).filter
        (candidateIsChild ∘ attachment.freshRegion) =
      (Data.Finite.allFin
        attachment.fragmentRegions.length).filter
        (fragmentIsChild ∘
          attachment.fragmentRegions.get) := by
    apply List.filter_congr
    intro fresh _
    unfold candidateIsChild fragmentIsChild
    simp only [Function.comp_apply]
    cases data :
        fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh) with
    | sheet =>
        rw [
          ConcreteSpliceAttachment.diagram_region_freshRegion,
          data]
        rfl
    | cut parent =>
        rw [
          ConcreteSpliceAttachment.diagram_region_freshRegion,
          data]
        simp only [mapRegion]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact ⟨fun same =>
            fragmentRegion_injective attachment same,
          fun same =>
            congrArg attachment.fragmentRegion same⟩
  have sourceList :
      List.map attachment.fragmentRegions.get
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (fragmentIsChild ∘
              attachment.fragmentRegions.get)) =
        fragment.val.diagram.regionsList.filter
          fragmentIsChild := by
    rw [← List.filter_map, map_get_allFin]
    unfold ConcreteSpliceAttachment.fragmentRegions
    rw [List.filter_filter]
    apply List.filter_congr
    intro sourceRegion _
    by_cases root :
        sourceRegion = fragment.val.diagram.root
    · subst sourceRegion
      unfold fragmentIsChild
      rw [fragment.property.diagram.root_is_sheet]
      rfl
    · have decided :
          decide
            (sourceRegion ≠ fragment.val.diagram.root) = true :=
        decide_eq_true root
      rw [decided]
      unfold fragmentIsChild
      cases fragment.val.diagram.regions sourceRegion <;>
        simp only [Bool.and_true]
  let hostPart :=
    List.map attachment.hostRegion
      ((Data.Finite.allFin
        removed.complement.val.regionCount).filter
        (candidateIsChild ∘ attachment.hostRegion))
  let freshPart :=
    List.map attachment.freshRegion
      ((Data.Finite.allFin
        attachment.fragmentRegions.length).filter
        (candidateIsChild ∘ attachment.freshRegion))
  let sourcePart :=
    List.map attachment.fragmentRegion
      (fragment.val.diagram.regionsList.filter
        fragmentIsChild)
  change hostPart ++ freshPart = sourcePart
  have hostPartEmpty : hostPart = [] :=
    congrArg (List.map attachment.hostRegion) hostEmpty
  have freshPartExact : freshPart = sourcePart := by
    dsimp only [freshPart, sourcePart]
    rw [freshFilter]
    calc
      _ = List.map
            (fun fresh =>
              attachment.fragmentRegion
                (attachment.fragmentRegions.get fresh))
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (fragmentIsChild ∘
                attachment.fragmentRegions.get)) := by
          apply List.map_congr_left
          intro fresh _
          exact (fragmentRegion_internal attachment fresh).symm
      _ = _ := by
        simpa only [List.map_map, Function.comp_apply] using
          congrArg (List.map attachment.fragmentRegion) sourceList
  rw [hostPartEmpty, freshPartExact]
  rfl

end RemovalFactorization

end VisualProof
