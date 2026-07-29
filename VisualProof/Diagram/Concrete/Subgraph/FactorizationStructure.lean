import VisualProof.Diagram.Concrete.Subgraph.Factorization

namespace VisualProof

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

namespace InsertionCompilation

private theorem hostRegion_injective
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Function.Injective attachment.hostRegion := by
  intro left right same
  apply Fin.ext
  simpa [ConcreteSpliceAttachment.hostRegion] using
    congrArg Fin.val same

private theorem origin_mem
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value : Var
      (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => exact nomatch value
  | cons head tail induction =>
      cases value with
      | here => simp [ConcreteElaboration.WireContext.origin]
      | there rest =>
          exact List.mem_cons_of_mem head (induction rest)

/-- Acceptance through `compileInsertion?` certifies the raw generated table. -/
theorem generated_wellFormed
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    attachment.diagram.WellFormed definitions :=
  splice_success_wellFormed compiled.candidate_accepted

/-- Every supplied target occurs in the compiler-visible insertion context. -/
theorem target_visible
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (position : Fin fragment.val.boundary.length) :
    attachment.target position ∈ compiled.site.frame.visible.ids := by
  cases packed : compiled.targetPackedAt position with
  | mk sig value =>
      have member :=
        origin_mem base.val compiled.site.frame.visible.ids value
      have exactOrigin := compiled.targetPackedAt_origin position
      rw [packed] at exactOrigin
      exact exactOrigin ▸ member

/-- The host and fresh region maps partition the generated region carrier. -/
theorem region_allocations
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment) :
    Data.Finite.allFin attachment.regionCount =
      (Data.Finite.allFin base.val.regionCount).map attachment.hostRegion ++
        (Data.Finite.allFin attachment.fragmentRegions.length).map
          attachment.freshRegion := by
  change
    Data.Finite.allFin
        (base.val.regionCount + attachment.fragmentRegions.length) = _
  exact allFin_add _ _

/-- Host, fragment, and grouped-identity maps partition generated nodes. -/
theorem node_allocations
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment) :
    Data.Finite.allFin attachment.nodeCount =
      (Data.Finite.allFin base.val.nodeCount).map attachment.hostNode ++
        (Data.Finite.allFin fragment.val.diagram.nodeCount).map
            attachment.fragmentNode ++
          (Data.Finite.allFin attachment.identityRequests.length).map
            attachment.identityNode := by
  change
    Data.Finite.allFin
        (base.val.nodeCount +
          (fragment.val.diagram.nodeCount +
            attachment.identityRequests.length)) = _
  rw [allFin_add, allFin_add, List.map_append, List.map_map,
    List.map_map, List.append_assoc]
  congr 1
  congr 1
  · apply List.map_congr_left
    intro node _
    apply Fin.ext
    simp [ConcreteSpliceAttachment.identityNode]
    omega

/-- Host and fresh maps partition the generated wire carrier. -/
theorem wire_allocations
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment) :
    Data.Finite.allFin attachment.wireCount =
      (Data.Finite.allFin base.val.wireCount).map attachment.hostWire ++
        (Data.Finite.allFin attachment.fragmentInternalWires.length).map
          attachment.freshWire := by
  change
    Data.Finite.allFin
        (base.val.wireCount + attachment.fragmentInternalWires.length) = _
  exact allFin_add _ _

/-- The fragment root is identified with exactly the explicit base site. -/
theorem fragmentRegion_eq_site_iff
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId) :
    attachment.fragmentRegion region = attachment.hostRegion site ↔
      region = fragment.val.diagram.root := by
  constructor
  · intro same
    by_cases root : region = fragment.val.diagram.root
    · exact root
    · unfold ConcreteSpliceAttachment.fragmentRegion at same
      simp only [root, ↓reduceDIte] at same
      exact
        (attachment.hostRegion_ne_freshRegion site _ same.symm).elim
  · rintro rfl
    simp [ConcreteSpliceAttachment.fragmentRegion]

private theorem fragmentInternalWires_nodup
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    attachment.fragmentInternalWires.Nodup :=
  (Data.Finite.allFin_nodup fragment.val.diagram.wireCount).filter _

private theorem fragmentInternalWire_not_boundary
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    attachment.fragmentInternalWires.get fresh ∉ fragment.val.boundary := by
  have member := List.get_mem attachment.fragmentInternalWires fresh
  simpa [ConcreteSpliceAttachment.fragmentInternalWires,
    ConcreteDiagram.wiresList] using
    (List.mem_filter.mp member).2

/-- Every enumerated internal fragment wire maps to its exact fresh index. -/
theorem fragmentWire_internal
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
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

private theorem fragmentRegions_nodup
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    attachment.fragmentRegions.Nodup :=
  (Data.Finite.allFin_nodup fragment.val.diagram.regionCount).filter _

private theorem fragmentRegion_nonroot
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (fresh : Fin attachment.fragmentRegions.length) :
    attachment.fragmentRegions.get fresh ≠ fragment.val.diagram.root := by
  have member := List.get_mem attachment.fragmentRegions fresh
  simpa [ConcreteSpliceAttachment.fragmentRegions,
    ConcreteDiagram.regionsList] using
    (List.mem_filter.mp member).2

/-- Every enumerated nonroot fragment region maps to its exact fresh index. -/
theorem fragmentRegion_internal
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (fresh : Fin attachment.fragmentRegions.length) :
    attachment.fragmentRegion (attachment.fragmentRegions.get fresh) =
      attachment.freshRegion fresh := by
  unfold ConcreteSpliceAttachment.fragmentRegion
  simp only [fragmentRegion_nonroot attachment fresh, ↓reduceDIte]
  congr 1
  exact DenseList.index_get attachment.fragmentRegions
    (fragmentRegions_nodup attachment) fresh

/-- One grouped request produces one n-ary identity node at the site. -/
theorem identity_node
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (identity : Fin attachment.identityRequests.length) :
    attachment.diagram.nodes (attachment.identityNode identity) =
      .identity (attachment.hostRegion site)
        (attachment.identityRequests.get identity).sig
        (attachment.identityRequests.get identity).attachments.length :=
      attachment.diagram_node_identityNode identity

/-- A generated host region is exactly the base region under host transport. -/
theorem host_region_source
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId) :
    attachment.diagram.regions (attachment.hostRegion region) =
      mapRegion attachment.hostRegion (base.val.regions region) :=
  attachment.diagram_region_hostRegion region

/-- A generated fresh region is exactly its enumerated fragment source. -/
theorem fresh_region_source
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (fresh : Fin attachment.fragmentRegions.length) :
    attachment.diagram.regions (attachment.freshRegion fresh) =
      mapRegion attachment.fragmentRegion
        (fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh)) :=
  attachment.diagram_region_freshRegion fresh

/-- A generated host node is exactly the renamed base node. -/
theorem host_node_source
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (node : base.val.NodeId) :
    attachment.diagram.nodes (attachment.hostNode node) =
      ConcreteSpliceAttachment.renameHostNode attachment node :=
  attachment.diagram_node_hostNode node

/-- A generated fragment node is exactly its renamed fragment source. -/
theorem fragment_node_source
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (node : fragment.val.diagram.NodeId) :
    attachment.diagram.nodes (attachment.fragmentNode node) =
      ConcreteSpliceAttachment.renameFragmentNode attachment node :=
  attachment.diagram_node_fragmentNode node

/-- A retained host wire keeps its exact signature and transported scope. -/
theorem host_wire_source
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (wire : base.val.WireId) :
    (attachment.diagram.wires (attachment.hostWire wire)).sig =
        (base.val.wires wire).sig ∧
      (attachment.diagram.wires (attachment.hostWire wire)).scope =
        attachment.hostRegion (base.val.wires wire).scope :=
  ⟨attachment.diagram_wire_hostWire wire,
    attachment.diagram_wire_hostWire_scope wire⟩

/-- A fresh wire keeps its enumerated fragment signature and transported scope. -/
theorem fresh_wire_source
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    (attachment.diagram.wires (attachment.freshWire fresh)).sig =
        (fragment.val.diagram.wires
          (attachment.fragmentInternalWires.get fresh)).sig ∧
      (attachment.diagram.wires (attachment.freshWire fresh)).scope =
        attachment.fragmentRegion
          (fragment.val.diagram.wires
            (attachment.fragmentInternalWires.get fresh)).scope := by
  constructor
  · unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
      ConcreteSpliceAttachment.freshWire
    simp only [Fin.addCases_right]
  · exact attachment.diagram_wire_freshWire_scope fresh

/--
The generated site wire table retains base-local wires as a prefix and then
the fragment's internal root-local wires in their source order.
-/
theorem site_wires
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    attachment.diagram.wiresAt (attachment.hostRegion site) =
      (base.val.wiresAt site).map attachment.hostWire ++
        (ConcreteElaboration.openRootLocalWires fragment.val).map
          attachment.fragmentWire := by
  have hostFilter :
      (Data.Finite.allFin base.val.wireCount).filter
          (fun wire =>
            (attachment.diagram.wires
                (attachment.hostWire wire)).scope ==
              attachment.hostRegion site) =
        base.val.wiresAt site := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    apply List.filter_congr
    intro wire _
    simp only [
      ConcreteSpliceAttachment.diagram_wire_hostWire_scope]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact
      ⟨fun same => hostRegion_injective attachment same,
        fun same => congrArg attachment.hostRegion same⟩
  have freshFilter :
      (Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (fun fresh =>
            (attachment.diagram.wires
                (attachment.freshWire fresh)).scope ==
              attachment.hostRegion site) =
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
    exact compiled.fragmentRegion_eq_site_iff _
  have hostMapped :
      List.map attachment.hostWire
        ((Data.Finite.allFin base.val.wireCount).filter
          (((fun wire =>
            (attachment.diagram.wires wire).scope ==
              attachment.hostRegion site)) ∘ attachment.hostWire)) =
        (base.val.wiresAt site).map attachment.hostWire := by
    have exactFilter :
        (Data.Finite.allFin base.val.wireCount).filter
            (((fun wire =>
              (attachment.diagram.wires wire).scope ==
                attachment.hostRegion site)) ∘ attachment.hostWire) =
          base.val.wiresAt site := by
      simpa only [Function.comp_apply] using hostFilter
    exact congrArg (List.map attachment.hostWire) exactFilter
  have freshMapped :
      List.map attachment.freshWire
        ((Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (((fun wire =>
            (attachment.diagram.wires wire).scope ==
              attachment.hostRegion site)) ∘ attachment.freshWire)) =
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
                attachment.hostRegion site)) ∘ attachment.freshWire) =
          (Data.Finite.allFin
            attachment.fragmentInternalWires.length).filter
            (fun fresh =>
              (fragment.val.diagram.wires
                  (attachment.fragmentInternalWires.get fresh)).scope ==
                fragment.val.diagram.root) := by
      simpa only [Function.comp_apply] using freshFilter
    rw [exactFilter]
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
    simp [ConcreteElaboration.openBoundaryWires, Bool.and_comm]
  have freshAsFragment :
      ((Data.Finite.allFin
        attachment.fragmentInternalWires.length).filter
        (fun fresh =>
          (fragment.val.diagram.wires
              (attachment.fragmentInternalWires.get fresh)).scope ==
            fragment.val.diagram.root)).map attachment.freshWire =
        (ConcreteElaboration.openRootLocalWires fragment.val).map
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
        exact (compiled.fragmentWire_internal fresh).symm]
    simpa only [List.map_map, Function.comp_apply] using
      congrArg (List.map attachment.fragmentWire) sourceList
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  change (Data.Finite.allFin attachment.wireCount).filter _ = _
  rw [compiled.wire_allocations, List.filter_append,
    List.filter_map, List.filter_map]
  exact
    (congrArg (fun hostPart =>
        hostPart ++
          List.map attachment.freshWire
            ((Data.Finite.allFin
              attachment.fragmentInternalWires.length).filter
              (((fun wire =>
                (attachment.diagram.wires wire).scope ==
                  attachment.hostRegion site)) ∘ attachment.freshWire)))
      hostMapped).trans
      ((congrArg
        (fun freshPart =>
          (base.val.wiresAt site).map attachment.hostWire ++ freshPart)
        freshMapped).trans
        (congrArg
          (fun freshPart =>
            (base.val.wiresAt site).map attachment.hostWire ++ freshPart)
          freshAsFragment))

/--
The generated site node table retains base nodes as a prefix, followed by
fragment-root nodes and then one grouped n-ary identity node per request.
-/
theorem site_nodes
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    attachment.diagram.nodesAt (attachment.hostRegion site) =
      (base.val.nodesAt site).map attachment.hostNode ++
        (fragment.val.diagram.nodesAt fragment.val.diagram.root).map
            attachment.fragmentNode ++
          (Data.Finite.allFin attachment.identityRequests.length).map
            attachment.identityNode := by
  have hostFilter :
      (Data.Finite.allFin base.val.nodeCount).filter
          (fun node =>
            (attachment.diagram.nodes
                (attachment.hostNode node)).region ==
              attachment.hostRegion site) =
        base.val.nodesAt site := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.filter_congr
    intro node _
    simp only [
      ConcreteSpliceAttachment.diagram_node_hostNode_region]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact
      ⟨fun same => hostRegion_injective attachment same,
        fun same => congrArg attachment.hostRegion same⟩
  have fragmentFilter :
      (Data.Finite.allFin fragment.val.diagram.nodeCount).filter
          (fun node =>
            (attachment.diagram.nodes
                (attachment.fragmentNode node)).region ==
              attachment.hostRegion site) =
        fragment.val.diagram.nodesAt fragment.val.diagram.root := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.filter_congr
    intro node _
    simp only [
      ConcreteSpliceAttachment.diagram_node_fragmentNode_region]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact compiled.fragmentRegion_eq_site_iff _
  have identityFilter :
      (Data.Finite.allFin attachment.identityRequests.length).filter
          (fun identity =>
            (attachment.diagram.nodes
                (attachment.identityNode identity)).region ==
              attachment.hostRegion site) =
        Data.Finite.allFin attachment.identityRequests.length := by
    apply List.filter_eq_self.mpr
    intro identity _
    rw [compiled.identity_node identity]
    simp [CNode.region]
  have hostFilter' :
      (Data.Finite.allFin base.val.nodeCount).filter
          (((fun node =>
            (attachment.diagram.nodes node).region ==
              attachment.hostRegion site)) ∘ attachment.hostNode) =
        base.val.nodesAt site := by
    simpa only [Function.comp_apply] using hostFilter
  have fragmentFilter' :
      (Data.Finite.allFin fragment.val.diagram.nodeCount).filter
          (((fun node =>
            (attachment.diagram.nodes node).region ==
              attachment.hostRegion site)) ∘ attachment.fragmentNode) =
        fragment.val.diagram.nodesAt fragment.val.diagram.root := by
    simpa only [Function.comp_apply] using fragmentFilter
  have identityFilter' :
      (Data.Finite.allFin attachment.identityRequests.length).filter
          (((fun node =>
            (attachment.diagram.nodes node).region ==
              attachment.hostRegion site)) ∘ attachment.identityNode) =
        Data.Finite.allFin attachment.identityRequests.length := by
    simpa only [Function.comp_apply] using identityFilter
  have hostMapped :
      List.map attachment.hostNode
          ((Data.Finite.allFin base.val.nodeCount).filter
            (((fun node =>
              (attachment.diagram.nodes node).region ==
                attachment.hostRegion site)) ∘ attachment.hostNode)) =
        List.map attachment.hostNode
          ((Data.Finite.allFin base.val.nodeCount).filter
            (fun node => (base.val.nodes node).region == site)) := by
    simpa [ConcreteDiagram.nodesAt, ConcreteDiagram.nodesList] using
      congrArg (List.map attachment.hostNode) hostFilter'
  have fragmentMapped :
      List.map attachment.fragmentNode
          ((Data.Finite.allFin fragment.val.diagram.nodeCount).filter
            (((fun node =>
              (attachment.diagram.nodes node).region ==
                attachment.hostRegion site)) ∘ attachment.fragmentNode)) =
        List.map attachment.fragmentNode
          ((Data.Finite.allFin fragment.val.diagram.nodeCount).filter
            (fun node =>
              (fragment.val.diagram.nodes node).region ==
                fragment.val.diagram.root)) := by
    simpa [ConcreteDiagram.nodesAt, ConcreteDiagram.nodesList] using
      congrArg (List.map attachment.fragmentNode) fragmentFilter'
  have identityMapped :
      List.map attachment.identityNode
          ((Data.Finite.allFin attachment.identityRequests.length).filter
            (((fun node =>
              (attachment.diagram.nodes node).region ==
                attachment.hostRegion site)) ∘ attachment.identityNode)) =
        List.map attachment.identityNode
          (Data.Finite.allFin attachment.identityRequests.length) :=
    congrArg (List.map attachment.identityNode) identityFilter'
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change
    (Data.Finite.allFin attachment.nodeCount).filter _ = _
  rw [compiled.node_allocations, List.filter_append,
    List.filter_append, List.filter_map, List.filter_map,
    List.filter_map]
  calc
    _ =
        List.map attachment.hostNode
              ((Data.Finite.allFin base.val.nodeCount).filter
                (fun node => (base.val.nodes node).region == site)) ++
            List.map attachment.fragmentNode
              ((Data.Finite.allFin fragment.val.diagram.nodeCount).filter
                (((fun node =>
                  (attachment.diagram.nodes node).region ==
                    attachment.hostRegion site)) ∘
                  attachment.fragmentNode)) ++
          List.map attachment.identityNode
            ((Data.Finite.allFin
              attachment.identityRequests.length).filter
              (((fun node =>
                (attachment.diagram.nodes node).region ==
                  attachment.hostRegion site)) ∘
                attachment.identityNode)) :=
      congrArg
        (fun hostPart =>
          (hostPart ++
            List.map attachment.fragmentNode
              ((Data.Finite.allFin
                fragment.val.diagram.nodeCount).filter
                (((fun node =>
                  (attachment.diagram.nodes node).region ==
                    attachment.hostRegion site)) ∘
                  attachment.fragmentNode))) ++
            List.map attachment.identityNode
              ((Data.Finite.allFin
                attachment.identityRequests.length).filter
                (((fun node =>
                  (attachment.diagram.nodes node).region ==
                    attachment.hostRegion site)) ∘
                  attachment.identityNode)))
        hostMapped
    _ =
        List.map attachment.hostNode
              ((Data.Finite.allFin base.val.nodeCount).filter
                (fun node => (base.val.nodes node).region == site)) ++
            List.map attachment.fragmentNode
              ((Data.Finite.allFin
                fragment.val.diagram.nodeCount).filter
                (fun node =>
                  (fragment.val.diagram.nodes node).region ==
                    fragment.val.diagram.root)) ++
          List.map attachment.identityNode
            ((Data.Finite.allFin
              attachment.identityRequests.length).filter
              (((fun node =>
                (attachment.diagram.nodes node).region ==
                  attachment.hostRegion site)) ∘
                attachment.identityNode)) :=
      congrArg
        (fun fragmentPart =>
          (List.map attachment.hostNode
              ((Data.Finite.allFin base.val.nodeCount).filter
                (fun node => (base.val.nodes node).region == site)) ++
            fragmentPart) ++
            List.map attachment.identityNode
              ((Data.Finite.allFin
                attachment.identityRequests.length).filter
                (((fun node =>
                  (attachment.diagram.nodes node).region ==
                    attachment.hostRegion site)) ∘
                  attachment.identityNode)))
        fragmentMapped
    _ = _ :=
      congrArg
        (fun identityPart =>
          (List.map attachment.hostNode
              ((Data.Finite.allFin base.val.nodeCount).filter
                (fun node => (base.val.nodes node).region == site)) ++
            List.map attachment.fragmentNode
              ((Data.Finite.allFin
                fragment.val.diagram.nodeCount).filter
                (fun node =>
                  (fragment.val.diagram.nodes node).region ==
                    fragment.val.diagram.root))) ++
            identityPart)
        identityMapped

/--
The generated site's child table retains base children as a prefix followed
by the fragment root's children in their source order.
-/
theorem site_children
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    attachment.diagram.childrenOf (attachment.hostRegion site) =
      (base.val.childrenOf site).map attachment.hostRegion ++
        (fragment.val.diagram.childrenOf
          fragment.val.diagram.root).map attachment.fragmentRegion := by
  let generatedIsChild : attachment.diagram.RegionId → Bool :=
    fun child =>
      match attachment.diagram.regions child with
      | .sheet => false
      | .cut parent => parent == attachment.hostRegion site
  let fragmentIsChild : fragment.val.diagram.RegionId → Bool :=
    fun child =>
      match fragment.val.diagram.regions child with
      | .sheet => false
      | .cut parent => parent == fragment.val.diagram.root
  have generatedChildren :
      attachment.diagram.childrenOf (attachment.hostRegion site) =
        attachment.diagram.regionsList.filter generatedIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold generatedIsChild
    cases attachment.diagram.regions child <;> rfl
  have fragmentChildren :
      fragment.val.diagram.childrenOf fragment.val.diagram.root =
        fragment.val.diagram.regionsList.filter fragmentIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold fragmentIsChild
    cases fragment.val.diagram.regions child <;> rfl
  have hostFilter :
      (Data.Finite.allFin base.val.regionCount).filter
          (generatedIsChild ∘ attachment.hostRegion) =
        base.val.childrenOf site := by
    unfold generatedIsChild
    unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
    apply List.filter_congr
    intro child _
    simp only [Function.comp_apply]
    cases data : base.val.regions child with
    | sheet =>
        simp [data, mapRegion]
    | cut parent =>
        simp only [
          ConcreteSpliceAttachment.diagram_region_hostRegion,
          data, mapRegion]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact
          ⟨fun same => hostRegion_injective attachment same,
            fun same => congrArg attachment.hostRegion same⟩
  have freshFilter :
      (Data.Finite.allFin attachment.fragmentRegions.length).filter
          (generatedIsChild ∘ attachment.freshRegion) =
        (Data.Finite.allFin attachment.fragmentRegions.length).filter
          (fragmentIsChild ∘ attachment.fragmentRegions.get) := by
    unfold generatedIsChild fragmentIsChild
    apply List.filter_congr
    intro fresh _
    simp only [Function.comp_apply]
    cases data :
        fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh) with
    | sheet =>
        rw [ConcreteSpliceAttachment.diagram_region_freshRegion, data]
        rfl
    | cut parent =>
        rw [ConcreteSpliceAttachment.diagram_region_freshRegion, data]
        simp only [mapRegion]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact compiled.fragmentRegion_eq_site_iff parent
  have allocatedFilter :
      attachment.diagram.regionsList.filter generatedIsChild =
        List.map attachment.hostRegion
            ((Data.Finite.allFin base.val.regionCount).filter
              (generatedIsChild ∘ attachment.hostRegion)) ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (generatedIsChild ∘ attachment.freshRegion)) := by
    unfold ConcreteDiagram.regionsList
    change
      (Data.Finite.allFin attachment.regionCount).filter
          generatedIsChild = _
    rw [compiled.region_allocations]
    have split :=
      List.filter_append
        (p := generatedIsChild)
        ((Data.Finite.allFin base.val.regionCount).map
          attachment.hostRegion)
        ((Data.Finite.allFin attachment.fragmentRegions.length).map
          attachment.freshRegion)
    have hostExact :=
      List.filter_map
        (f := attachment.hostRegion) (p := generatedIsChild)
        (l := Data.Finite.allFin base.val.regionCount)
    have freshExact :=
      List.filter_map
        (f := attachment.freshRegion) (p := generatedIsChild)
        (l := Data.Finite.allFin attachment.fragmentRegions.length)
    exact
      split.trans
        ((congrArg
          (fun hostPart : List attachment.diagram.RegionId =>
            hostPart ++
              List.filter generatedIsChild
                ((Data.Finite.allFin
                  attachment.fragmentRegions.length).map
                  attachment.freshRegion))
          hostExact).trans
          (congrArg
            (fun freshPart : List attachment.diagram.RegionId =>
              (show List attachment.diagram.RegionId from
                List.map attachment.hostRegion
                    (List.filter
                      (generatedIsChild ∘ attachment.hostRegion)
                      (Data.Finite.allFin base.val.regionCount))) ++
                freshPart)
            freshExact))
  have sourceList :
      List.map attachment.fragmentRegions.get
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (fragmentIsChild ∘ attachment.fragmentRegions.get)) =
        fragment.val.diagram.regionsList.filter fragmentIsChild := by
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
  have hostMapped :
      List.map attachment.hostRegion
          ((Data.Finite.allFin base.val.regionCount).filter
            (generatedIsChild ∘ attachment.hostRegion)) =
        (base.val.childrenOf site).map attachment.hostRegion :=
    congrArg (List.map attachment.hostRegion) hostFilter
  have freshMapped :
      List.map attachment.freshRegion
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (generatedIsChild ∘ attachment.freshRegion)) =
        (fragment.val.diagram.childrenOf
          fragment.val.diagram.root).map attachment.fragmentRegion := by
    have candidateSources :
        List.map attachment.fragmentRegions.get
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (generatedIsChild ∘ attachment.freshRegion)) =
          fragment.val.diagram.regionsList.filter fragmentIsChild :=
      (congrArg (List.map attachment.fragmentRegions.get)
        freshFilter).trans sourceList
    have freshAsFragment :
        List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (generatedIsChild ∘ attachment.freshRegion)) =
          List.map
            (fun fresh =>
              attachment.fragmentRegion
                (attachment.fragmentRegions.get fresh))
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (generatedIsChild ∘ attachment.freshRegion)) := by
      apply List.map_congr_left
      intro fresh _
      exact (compiled.fragmentRegion_internal fresh).symm
    rw [freshAsFragment]
    rw [fragmentChildren]
    simpa only [List.map_map, Function.comp_apply] using
      congrArg (List.map attachment.fragmentRegion) candidateSources
  rw [generatedChildren]
  exact
    allocatedFilter.trans
      ((congrArg
        (fun hostPart =>
          hostPart ++
            List.map attachment.freshRegion
              ((Data.Finite.allFin
                attachment.fragmentRegions.length).filter
                (generatedIsChild ∘ attachment.freshRegion)))
        hostMapped).trans
        (congrArg
          (fun freshPart =>
            (base.val.childrenOf site).map attachment.hostRegion ++
              freshPart)
          freshMapped))

private theorem fragmentRegion_injective
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    Function.Injective attachment.fragmentRegion := by
  intro left right same
  by_cases leftRoot : left = fragment.val.diagram.root
  · subst left
    have rightRoot :=
      (compiled.fragmentRegion_eq_site_iff right).mp
        (by simpa [ConcreteSpliceAttachment.fragmentRegion] using same.symm)
    exact rightRoot.symm
  · by_cases rightRoot : right = fragment.val.diagram.root
    · subst right
      have leftRoot' :=
        (compiled.fragmentRegion_eq_site_iff left).mp
          (by simpa [ConcreteSpliceAttachment.fragmentRegion] using same)
      exact (leftRoot leftRoot').elim
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

/-- A copied nonroot fragment region contains exactly its copied nodes. -/
theorem fragment_nodes
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    attachment.diagram.nodesAt (attachment.fragmentRegion region) =
      (fragment.val.diagram.nodesAt region).map
        attachment.fragmentNode := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change (Data.Finite.allFin attachment.nodeCount).filter _ = _
  rw [compiled.node_allocations, List.filter_append,
    List.filter_append, List.filter_map, List.filter_map,
    List.filter_map]
  have hostEmpty :
      (Data.Finite.allFin base.val.nodeCount).filter
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
    exact
      ⟨fun same => fragmentRegion_injective compiled same,
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
      ((Data.Finite.allFin base.val.nodeCount).filter
        (((fun node =>
          (attachment.diagram.nodes node).region ==
            attachment.fragmentRegion region) ∘
          attachment.hostNode)))
  let fragmentPart :=
    List.map attachment.fragmentNode
      ((Data.Finite.allFin fragment.val.diagram.nodeCount).filter
        (((fun node =>
          (attachment.diagram.nodes node).region ==
            attachment.fragmentRegion region) ∘
          attachment.fragmentNode)))
  let identityPart :=
    List.map attachment.identityNode
      ((Data.Finite.allFin attachment.identityRequests.length).filter
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

/-- A copied nonroot fragment region contains exactly its copied local wires. -/
theorem fragment_wires
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    attachment.diagram.wiresAt (attachment.fragmentRegion region) =
      (fragment.val.diagram.wiresAt region).map
        attachment.fragmentWire := by
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  change (Data.Finite.allFin attachment.wireCount).filter _ = _
  rw [compiled.wire_allocations, List.filter_append,
    List.filter_map, List.filter_map]
  have hostEmpty :
      (Data.Finite.allFin base.val.wireCount).filter
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
    exact
      ⟨fun same => fragmentRegion_injective compiled same,
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
      ((Data.Finite.allFin base.val.wireCount).filter
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
          exact (compiled.fragmentWire_internal fresh).symm
      _ = _ := by
        simpa only [List.map_map, Function.comp_apply] using
          congrArg (List.map attachment.fragmentWire) sourceList
  rw [hostPartEmpty, freshPartExact]
  rfl

/-- A copied nonroot fragment region contains exactly its copied children. -/
theorem fragment_children
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    attachment.diagram.childrenOf
        (attachment.fragmentRegion region) =
      (fragment.val.diagram.childrenOf region).map
        attachment.fragmentRegion := by
  let generatedIsChild : attachment.diagram.RegionId → Bool :=
    fun child =>
      match attachment.diagram.regions child with
      | .sheet => false
      | .cut parent => parent == attachment.fragmentRegion region
  let fragmentIsChild : fragment.val.diagram.RegionId → Bool :=
    fun child =>
      match fragment.val.diagram.regions child with
      | .sheet => false
      | .cut parent => parent == region
  have generatedChildren :
      attachment.diagram.childrenOf
          (attachment.fragmentRegion region) =
        attachment.diagram.regionsList.filter generatedIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold generatedIsChild
    cases attachment.diagram.regions child <;> rfl
  have fragmentChildren :
      fragment.val.diagram.childrenOf region =
        fragment.val.diagram.regionsList.filter fragmentIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold fragmentIsChild
    cases fragment.val.diagram.regions child <;> rfl
  rw [generatedChildren, fragmentChildren]
  have allocations :
      attachment.diagram.regionsList =
        (Data.Finite.allFin base.val.regionCount).map
            attachment.hostRegion ++
          (Data.Finite.allFin
            attachment.fragmentRegions.length).map
              attachment.freshRegion := by
    unfold ConcreteDiagram.regionsList
    exact compiled.region_allocations
  have allocatedFilter :=
    congrArg (List.filter generatedIsChild) allocations
  have expanded :
      attachment.diagram.regionsList.filter generatedIsChild =
        List.map attachment.hostRegion
            ((Data.Finite.allFin base.val.regionCount).filter
              (generatedIsChild ∘ attachment.hostRegion)) ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (generatedIsChild ∘ attachment.freshRegion)) := by
    refine allocatedFilter.trans ?_
    calc
      List.filter generatedIsChild
          (List.map attachment.hostRegion
              (Data.Finite.allFin base.val.regionCount) ++
            List.map attachment.freshRegion
              (Data.Finite.allFin attachment.fragmentRegions.length)) =
          List.filter generatedIsChild
              (List.map attachment.hostRegion
                (Data.Finite.allFin base.val.regionCount)) ++
            List.filter generatedIsChild
              (List.map attachment.freshRegion
                (Data.Finite.allFin attachment.fragmentRegions.length)) :=
        List.filter_append _ _
      _ = _ := by
        rw [List.filter_map, List.filter_map]
        rfl
  rw [expanded]
  have hostEmpty :
      (Data.Finite.allFin base.val.regionCount).filter
        (generatedIsChild ∘ attachment.hostRegion) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro child member
    have accepted := (List.mem_filter.mp member).2
    unfold generatedIsChild at accepted
    simp only [Function.comp_apply] at accepted
    cases data : base.val.regions child with
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
        (generatedIsChild ∘ attachment.freshRegion) =
      (Data.Finite.allFin
        attachment.fragmentRegions.length).filter
        (fragmentIsChild ∘ attachment.fragmentRegions.get) := by
    apply List.filter_congr
    intro fresh _
    unfold generatedIsChild fragmentIsChild
    simp only [Function.comp_apply]
    cases data :
        fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh) with
    | sheet =>
        rw [ConcreteSpliceAttachment.diagram_region_freshRegion, data]
        rfl
    | cut parent =>
        rw [ConcreteSpliceAttachment.diagram_region_freshRegion, data]
        simp only [mapRegion]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact
          ⟨fun same => fragmentRegion_injective compiled same,
            fun same => congrArg attachment.fragmentRegion same⟩
  have sourceList :
      List.map attachment.fragmentRegions.get
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (fragmentIsChild ∘ attachment.fragmentRegions.get)) =
        fragment.val.diagram.regionsList.filter fragmentIsChild := by
    rw [← List.filter_map, map_get_allFin]
    unfold ConcreteSpliceAttachment.fragmentRegions
    rw [List.filter_filter]
    apply List.filter_congr
    intro sourceRegion _
    by_cases root : sourceRegion = fragment.val.diagram.root
    · subst sourceRegion
      unfold fragmentIsChild
      rw [fragment.property.diagram.root_is_sheet]
      rfl
    · have decided :
          decide (sourceRegion ≠ fragment.val.diagram.root) = true :=
        decide_eq_true root
      rw [decided]
      unfold fragmentIsChild
      cases fragment.val.diagram.regions sourceRegion <;>
        simp only [Bool.and_true]
  let hostPart :=
    List.map attachment.hostRegion
      ((Data.Finite.allFin base.val.regionCount).filter
        (generatedIsChild ∘ attachment.hostRegion))
  let freshPart :=
    List.map attachment.freshRegion
      ((Data.Finite.allFin
        attachment.fragmentRegions.length).filter
        (generatedIsChild ∘ attachment.freshRegion))
  let sourcePart :=
    List.map attachment.fragmentRegion
      (fragment.val.diagram.regionsList.filter fragmentIsChild)
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
          exact (compiled.fragmentRegion_internal fresh).symm
      _ = _ := by
        simpa only [List.map_map, Function.comp_apply] using
          congrArg (List.map attachment.fragmentRegion) sourceList
  rw [hostPartEmpty, freshPartExact]
  rfl

/-- Generated incidences are exactly fragment or grouped-identity incidences. -/
theorem generatedEndpoint_mem_iff
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (wire : attachment.diagram.WireId)
    (endpoint : CEndpoint attachment.nodeCount) :
    endpoint ∈ attachment.generatedEndpoints wire ↔
      (wire, endpoint) ∈
        attachment.fragmentEndpointOccurrences ++
          attachment.identityEndpointOccurrences := by
  unfold ConcreteSpliceAttachment.generatedEndpoints
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with
      ⟨occurrence, occurrenceMember, accepted⟩
    rcases occurrence with ⟨occurrenceWire, occurrenceEndpoint⟩
    split at accepted
    · rename_i same
      have endpointSame := Option.some.inj accepted
      cases same
      cases endpointSame
      exact occurrenceMember
    · contradiction
  · intro member
    exact List.mem_filterMap.mpr
      ⟨(wire, endpoint), member, by simp⟩

/-- A retained host wire keeps its endpoints as a prefix. -/
theorem host_wire_endpoints
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (wire : base.val.WireId) :
    (attachment.diagram.wires
        (attachment.hostWire wire)).endpoints =
      (base.val.wires wire).endpoints.map attachment.hostEndpoint ++
        attachment.generatedEndpoints (attachment.hostWire wire) := by
  unfold ConcreteSpliceAttachment.diagram
    ConcreteSpliceAttachment.wireTable
    ConcreteSpliceAttachment.hostWire
  simp only [Fin.addCases_left]

/-- A fresh fragment wire has exactly its generated fragment/identity endpoints. -/
theorem fresh_wire_endpoints
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    (attachment.diagram.wires
        (attachment.freshWire fresh)).endpoints =
      attachment.generatedEndpoints (attachment.freshWire fresh) := by
  unfold ConcreteSpliceAttachment.diagram
    ConcreteSpliceAttachment.wireTable
    ConcreteSpliceAttachment.freshWire
  simp only [Fin.addCases_right]

end InsertionCompilation

end VisualProof
