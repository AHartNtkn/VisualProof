import VisualProof.Diagram.Concrete.Subgraph.FactorizationRetarget

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

theorem hostRegion_injective
    (attachment : ConcreteSpliceAttachment removed fragment) :
    Function.Injective attachment.hostRegion := by
  intro left right same
  apply Fin.ext
  simpa [ConcreteSpliceAttachment.hostRegion] using congrArg Fin.val same

private theorem hostRegion_climb
    (attachment : ConcreteSpliceAttachment removed fragment) :
    ∀ steps region,
      attachment.diagram.climb steps
          (attachment.hostRegion region) =
        (removed.complement.val.climb steps region).map
          attachment.hostRegion := by
  intro steps
  induction steps with
  | zero => intro region; rfl
  | succ steps induction =>
      intro region
      cases data : removed.complement.val.regions region with
      | sheet =>
          simp [ConcreteDiagram.climb,
            ConcreteSpliceAttachment.diagram_region_hostRegion,
            data, mapRegion]
          rfl
      | cut parent =>
          simp [ConcreteDiagram.climb,
            ConcreteSpliceAttachment.diagram_region_hostRegion,
            data, mapRegion, induction parent]

private theorem fragmentRegion_eq_hostRegion_iff
    (attachment : ConcreteSpliceAttachment removed fragment)
    (fragmentRegion : fragment.val.diagram.RegionId)
    (hostRegion : removed.complement.val.RegionId) :
    attachment.fragmentRegion fragmentRegion =
        attachment.hostRegion hostRegion ↔
      fragmentRegion = fragment.val.diagram.root ∧
        hostRegion = removed.site := by
  constructor
  · intro same
    by_cases root : fragmentRegion = fragment.val.diagram.root
    · subst fragmentRegion
      refine ⟨rfl, hostRegion_injective attachment ?_⟩
      simpa [ConcreteSpliceAttachment.fragmentRegion] using same.symm
    · have impossible : False := by
        unfold ConcreteSpliceAttachment.fragmentRegion at same
        simp only [root, ↓reduceDIte] at same
        exact
          attachment.hostRegion_ne_freshRegion hostRegion _ same.symm
      exact impossible.elim
  · rintro ⟨rfl, rfl⟩
    simp [ConcreteSpliceAttachment.fragmentRegion]

/--
Outside the splice site, the candidate's locally scoped wires are exactly the
ordered `hostWire` image of the complement's locally scoped wires.
-/
theorem candidate_wiresAt_hostRegion_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    attachment.diagram.wiresAt (attachment.hostRegion region) =
      (removed.complement.val.wiresAt region).map
        attachment.hostWire := by
  have hostFilter :
      (Data.Finite.allFin removed.complement.val.wireCount).filter
          (fun wire =>
            (attachment.diagram.wires
                (attachment.hostWire wire)).scope ==
              attachment.hostRegion region) =
        removed.complement.val.wiresAt region := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    apply List.filter_congr
    intro wire _
    simp only [ConcreteSpliceAttachment.diagram_wire_hostWire_scope]
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
              attachment.hostRegion region) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro fresh _
    simp only [
      ConcreteSpliceAttachment.diagram_wire_freshWire_scope]
    intro equalTrue
    have same := eq_of_beq equalTrue
    have site := (fragmentRegion_eq_hostRegion_iff attachment
      (fragment.val.diagram.wires
        (attachment.fragmentInternalWires.get fresh)).scope region).mp same
    exact notSite site.2
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  change
    (Data.Finite.allFin
      (removed.complement.val.wireCount +
        attachment.fragmentInternalWires.length)).filter _ = _
  rw [allFin_add, List.filter_append, List.filter_map, List.filter_map]
  change
    List.map attachment.hostWire
          ((Data.Finite.allFin
            removed.complement.val.wireCount).filter
            (fun wire =>
              (attachment.diagram.wires
                  (attachment.hostWire wire)).scope ==
                attachment.hostRegion region)) ++
        List.map attachment.freshWire
          ((Data.Finite.allFin
            attachment.fragmentInternalWires.length).filter
            (fun fresh =>
              (attachment.diagram.wires
                  (attachment.freshWire fresh)).scope ==
                attachment.hostRegion region)) =
      _
  rw [hostFilter, freshFilter]
  simp [ConcreteDiagram.wiresAt, ConcreteDiagram.wiresList]

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

/--
Outside the splice site, the candidate's local nodes are exactly the ordered
`hostNode` image of the complement's local nodes.
-/
theorem candidate_nodesAt_hostRegion_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    attachment.diagram.nodesAt (attachment.hostRegion region) =
      (removed.complement.val.nodesAt region).map
        attachment.hostNode := by
  have hostFilter :
      (Data.Finite.allFin removed.complement.val.nodeCount).filter
          (fun node =>
            (attachment.diagram.nodes
                (attachment.hostNode node)).region ==
              attachment.hostRegion region) =
        removed.complement.val.nodesAt region := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.filter_congr
    intro node _
    simp only [ConcreteSpliceAttachment.diagram_node_hostNode_region]
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
              attachment.hostRegion region) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro node _
    simp only [ConcreteSpliceAttachment.diagram_node_fragmentNode_region]
    intro equalTrue
    have same := eq_of_beq equalTrue
    have site :=
      (fragmentRegion_eq_hostRegion_iff attachment
        (fragment.val.diagram.nodes node).region region).mp same
    exact notSite site.2
  have identityFilter :
      (Data.Finite.allFin attachment.identityRequests.length).filter
          (fun identity =>
            (attachment.diagram.nodes
                (attachment.identityNode identity)).region ==
              attachment.hostRegion region) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro identity _
    rw [ConcreteSpliceAttachment.diagram_node_identityNode]
    simp only [CNode.region]
    intro equalTrue
    have mappedSame :
        attachment.hostRegion removed.site =
          attachment.hostRegion region := by
      simpa only [beq_iff_eq] using equalTrue
    have same := hostRegion_injective attachment mappedSame
    exact notSite same.symm
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change
    (Data.Finite.allFin attachment.nodeCount).filter _ =
      _
  rw [candidate_node_allocations, List.filter_append,
    List.filter_append, List.filter_map, List.filter_map,
    List.filter_map]
  change
    List.map attachment.hostNode
          ((Data.Finite.allFin
            removed.complement.val.nodeCount).filter
            (fun node =>
              (attachment.diagram.nodes
                  (attachment.hostNode node)).region ==
                attachment.hostRegion region)) ++
        List.map attachment.fragmentNode
          ((Data.Finite.allFin
            fragment.val.diagram.nodeCount).filter
            (fun node =>
              (attachment.diagram.nodes
                  (attachment.fragmentNode node)).region ==
                attachment.hostRegion region)) ++
        List.map attachment.identityNode
          ((Data.Finite.allFin
            attachment.identityRequests.length).filter
            (fun identity =>
              (attachment.diagram.nodes
                  (attachment.identityNode identity)).region ==
                attachment.hostRegion region)) =
      _
  rw [hostFilter, fragmentFilter, identityFilter]
  simp [ConcreteDiagram.nodesAt, ConcreteDiagram.nodesList]

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

/--
Outside the splice site, the candidate's children are exactly the ordered
`hostRegion` image of the complement's children.
-/
theorem candidate_childrenOf_hostRegion_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    attachment.diagram.childrenOf (attachment.hostRegion region) =
      (removed.complement.val.childrenOf region).map
        attachment.hostRegion := by
  let candidateIsChild : attachment.diagram.RegionId → Bool :=
    fun child =>
      match attachment.diagram.regions child with
      | .sheet => false
      | .cut parent => parent == attachment.hostRegion region
  let sourceIsChild : removed.complement.val.RegionId → Bool :=
    fun child =>
      match removed.complement.val.regions child with
      | .sheet => false
      | .cut parent => parent == region
  have candidateChildren :
      attachment.diagram.childrenOf (attachment.hostRegion region) =
        attachment.diagram.regionsList.filter candidateIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold candidateIsChild
    cases attachment.diagram.regions child <;> rfl
  have sourceChildren :
      removed.complement.val.childrenOf region =
        removed.complement.val.regionsList.filter sourceIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold sourceIsChild
    cases removed.complement.val.regions child <;> rfl
  have hostFilter :
      (Data.Finite.allFin removed.complement.val.regionCount).filter
          (candidateIsChild ∘ attachment.hostRegion) =
        (Data.Finite.allFin removed.complement.val.regionCount).filter
          sourceIsChild := by
    apply List.filter_congr
    intro child _
    simp only [Function.comp_apply]
    unfold candidateIsChild sourceIsChild
    rw [ConcreteSpliceAttachment.diagram_region_hostRegion]
    cases data : removed.complement.val.regions child with
    | sheet =>
        simp [mapRegion]
    | cut parent =>
        simp only [mapRegion]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact
          ⟨fun same => hostRegion_injective attachment same,
            fun same => congrArg attachment.hostRegion same⟩
  have freshFilter :
      (Data.Finite.allFin attachment.fragmentRegions.length).filter
          (candidateIsChild ∘ attachment.freshRegion) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro fresh _
    simp only [Function.comp_apply]
    unfold candidateIsChild
    rw [ConcreteSpliceAttachment.diagram_region_freshRegion]
    cases data :
        fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh) with
    | sheet =>
        simp [mapRegion]
    | cut parent =>
        simp only [mapRegion]
        intro equalTrue
        have same :
            attachment.fragmentRegion parent =
              attachment.hostRegion region := by
          simpa only [beq_iff_eq] using equalTrue
        have site :=
          (fragmentRegion_eq_hostRegion_iff attachment parent region).mp
            same
        exact notSite site.2
  rw [candidateChildren, sourceChildren]
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
  rw [expandedFilter]
  have hostMapped :
      List.map attachment.hostRegion
          ((Data.Finite.allFin
            removed.complement.val.regionCount).filter
            (candidateIsChild ∘ attachment.hostRegion)) =
        List.map attachment.hostRegion
          ((Data.Finite.allFin
            removed.complement.val.regionCount).filter
            sourceIsChild) :=
    congrArg (List.map attachment.hostRegion) hostFilter
  have hostReplaced :
      List.map attachment.hostRegion
            ((Data.Finite.allFin
              removed.complement.val.regionCount).filter
              (candidateIsChild ∘ attachment.hostRegion)) ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (candidateIsChild ∘ attachment.freshRegion)) =
        List.map attachment.hostRegion
            ((Data.Finite.allFin
              removed.complement.val.regionCount).filter
              sourceIsChild) ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (candidateIsChild ∘ attachment.freshRegion)) :=
    congrArg
      (fun hostPart =>
        hostPart ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (candidateIsChild ∘ attachment.freshRegion)))
      hostMapped
  rw [hostReplaced]
  have freshMapped :
      List.map attachment.freshRegion
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (candidateIsChild ∘ attachment.freshRegion)) =
        [] := by
    simpa only [List.map_nil] using
      congrArg (List.map attachment.freshRegion) freshFilter
  rw [freshMapped]
  unfold ConcreteDiagram.regionsList
  simp

/-- The exact ordered image of a complement wire context in a splice candidate. -/
def hostWireContext
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val) :
    ConcreteElaboration.WireContext attachment.diagram :=
  ⟨context.ids.map attachment.hostWire⟩

theorem hostWireContext_sigs
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val) :
    (hostWireContext attachment context).sigs = context.sigs := by
  unfold hostWireContext ConcreteElaboration.WireContext.sigs
  rw [List.map_map]
  apply List.map_congr_left
  intro wire _
  exact attachment.diagram_wire_hostWire wire

private def hostWireSigsEq
    (attachment : ConcreteSpliceAttachment removed fragment) :
    (ids : List removed.complement.val.WireId) →
      (ids.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig) =
        ids.map
          (fun wire => (removed.complement.val.wires wire).sig)
  | [] => rfl
  | wire :: tail =>
      (congrArg
          (fun head => head ::
            ((tail.map attachment.hostWire).map
              (fun target => (attachment.diagram.wires target).sig)))
          (attachment.diagram_wire_hostWire wire)).trans
        (congrArg
          (List.cons (removed.complement.val.wires wire).sig)
          (hostWireSigsEq attachment tail))

/--
The typed positional renaming induced by the exact host-wire context image.
-/
private def castVar
    (equality : sourceSig = targetSig)
    (value : Var context sourceSig) :
    Var context targetSig :=
  equality ▸ value

private theorem extend_castVar_here
    (equality : sourceSig = targetSig)
    (env : Env pre context)
    (value : pre.Domain sourceSig) :
    env.extend value targetSig
        (castVar equality (.here :
          Var (sourceSig :: context) sourceSig)) =
      @Eq.ndrec Sig sourceSig (fun sig => pre.Domain sig)
        value targetSig equality := by
  cases equality
  rfl

@[simp] private theorem origin_castVar
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sourceSig targetSig : Sig}
    (equality : sourceSig = targetSig)
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sourceSig) :
    ConcreteElaboration.WireContext.origin diagram ids
        (castVar equality value) =
      ConcreteElaboration.WireContext.origin diagram ids value := by
  cases equality
  rfl

private def hostWireVars
    (attachment : ConcreteSpliceAttachment removed fragment) :
    (ids : List removed.complement.val.WireId) →
      WireRenaming
        (ids.map
          (fun wire => (removed.complement.val.wires wire).sig))
        ((ids.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig))
  | [], _, value => nomatch value
  | wire :: tail, _, .here =>
      castVar (attachment.diagram_wire_hostWire wire) .here
  | wire :: tail, _, .there value =>
      .there (hostWireVars attachment tail value)

def hostWireContextRenaming
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val) :
    WireRenaming context.sigs (hostWireContext attachment context).sigs :=
  fun {_} value => by
    change
      Var
        ((context.ids.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig)) _
    exact hostWireVars attachment context.ids value

private theorem hostWireVars_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    ∀ (ids : List removed.complement.val.WireId)
      {sig : Sig}
      (value :
        Var
          (ids.map
            (fun wire => (removed.complement.val.wires wire).sig))
          sig),
      ConcreteElaboration.WireContext.origin attachment.diagram
          (ids.map attachment.hostWire)
          (hostWireVars attachment ids value) =
        attachment.hostWire
          (ConcreteElaboration.WireContext.origin
            removed.complement.val ids value)
  | [], _, value => nomatch value
  | wire :: tail, _, .here => by
      rw [show
        hostWireVars attachment (wire :: tail)
            (.here :
              Var
                ((wire :: tail).map
                  (fun source =>
                    (removed.complement.val.wires source).sig))
                (removed.complement.val.wires wire).sig) =
          castVar (attachment.diagram_wire_hostWire wire)
            (.here :
              Var
                (((wire :: tail).map attachment.hostWire).map
                  (fun target =>
                    (attachment.diagram.wires target).sig))
                (attachment.diagram.wires
                  (attachment.hostWire wire)).sig) from rfl]
      change
        ConcreteElaboration.WireContext.origin attachment.diagram
            (attachment.hostWire wire ::
              tail.map attachment.hostWire)
            (castVar (attachment.diagram_wire_hostWire wire)
              (.here :
                Var
                  ((attachment.hostWire wire ::
                    tail.map attachment.hostWire).map
                    (fun target =>
                      (attachment.diagram.wires target).sig))
                  (attachment.diagram.wires
                    (attachment.hostWire wire)).sig)) =
          attachment.hostWire wire
      exact
        (origin_castVar attachment.diagram
          (attachment.hostWire wire :: tail.map attachment.hostWire)
          (attachment.diagram_wire_hostWire wire) .here).trans rfl
  | wire :: tail, _, .there value => by
      unfold hostWireVars
      simp only [ConcreteElaboration.WireContext.origin]
      exact hostWireVars_origin attachment tail value

def hostWireValuesToSource
    (attachment : ConcreteSpliceAttachment removed fragment)
    {pre : PreModel} :
    (ids : List removed.complement.val.WireId) →
      ConcreteElaboration.WireValues pre
        ((ids.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig)) →
      ConcreteElaboration.WireValues pre
        (ids.map
          (fun wire => (removed.complement.val.wires wire).sig))
  | [], .nil => .nil
  | wire :: tail, .cons head rest =>
      .cons
        (@Eq.ndrec Sig
          (attachment.diagram.wires
            (attachment.hostWire wire)).sig
          (fun sig => pre.Domain sig) head
          (removed.complement.val.wires wire).sig
          (attachment.diagram_wire_hostWire wire))
        (hostWireValuesToSource attachment tail rest)

def hostWireValuesToTarget
    (attachment : ConcreteSpliceAttachment removed fragment)
    {pre : PreModel} :
    (ids : List removed.complement.val.WireId) →
      ConcreteElaboration.WireValues pre
        (ids.map
          (fun wire => (removed.complement.val.wires wire).sig)) →
      ConcreteElaboration.WireValues pre
        ((ids.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig))
  | [], .nil => .nil
  | wire :: tail, .cons head rest =>
      .cons
        (@Eq.ndrec Sig
          (removed.complement.val.wires wire).sig
          (fun sig => pre.Domain sig) head
          (attachment.diagram.wires
            (attachment.hostWire wire)).sig
          (attachment.diagram_wire_hostWire wire).symm)
        (hostWireValuesToTarget attachment tail rest)

theorem wireValues_cast_cancel
    (equality : source = target)
    (values : ConcreteElaboration.WireValues pre source) :
    equality.symm ▸ (equality ▸ values) = values := by
  cases equality
  rfl

theorem hostWireValues_target_source
    (attachment : ConcreteSpliceAttachment removed fragment) :
    ∀ (ids : List removed.complement.val.WireId)
      (values :
        ConcreteElaboration.WireValues pre
          (ids.map
            (fun wire => (removed.complement.val.wires wire).sig))),
      hostWireValuesToSource attachment ids
          (hostWireValuesToTarget attachment ids values) =
        values := by
  intro ids
  induction ids with
  | nil =>
      intro values
      cases values
      rfl
  | cons wire tail induction =>
      intro values
      cases values with
      | cons head rest =>
          change
            ConcreteElaboration.WireValues.cons
                (@Eq.ndrec Sig
                  (attachment.diagram.wires
                    (attachment.hostWire wire)).sig
                  (fun sig => pre.Domain sig)
                  (@Eq.ndrec Sig
                    (removed.complement.val.wires wire).sig
                    (fun sig => pre.Domain sig) head
                    (attachment.diagram.wires
                      (attachment.hostWire wire)).sig
                    (attachment.diagram_wire_hostWire wire).symm)
                  (removed.complement.val.wires wire).sig
                  (attachment.diagram_wire_hostWire wire))
                (hostWireValuesToSource attachment tail
                  (hostWireValuesToTarget attachment tail rest)) =
              ConcreteElaboration.WireValues.cons head rest
          have headRoundTrip :
              @Eq.ndrec Sig
                  (attachment.diagram.wires
                    (attachment.hostWire wire)).sig
                  (fun sig => pre.Domain sig)
                  (@Eq.ndrec Sig
                    (removed.complement.val.wires wire).sig
                    (fun sig => pre.Domain sig) head
                    (attachment.diagram.wires
                      (attachment.hostWire wire)).sig
                    (attachment.diagram_wire_hostWire wire).symm)
                  (removed.complement.val.wires wire).sig
                  (attachment.diagram_wire_hostWire wire) =
                head := by
            have cancel :
                ∀ {left right : Sig} (same : left = right)
                  (value : pre.Domain left),
                  @Eq.ndrec Sig right (fun sig => pre.Domain sig)
                      (@Eq.ndrec Sig left (fun sig => pre.Domain sig)
                        value right same)
                      left same.symm =
                    value := by
              intro left right same value
              cases same
              rfl
            exact cancel
              (attachment.diagram_wire_hostWire wire).symm head
          rw [headRoundTrip, induction rest]

private def hostWireVarsAppend
    (attachment : ConcreteSpliceAttachment removed fragment)
    (right : List removed.complement.val.WireId) :
    (left : List removed.complement.val.WireId) →
      WireRenaming
        ((left ++ right).map
          (fun wire => (removed.complement.val.wires wire).sig))
        (((left.map attachment.hostWire) ++
            (right.map attachment.hostWire)).map
          (fun wire => (attachment.diagram.wires wire).sig))
  | [], _, value => hostWireVars attachment right value
  | wire :: tail, _, .here =>
      castVar (attachment.diagram_wire_hostWire wire) .here
  | wire :: tail, _, .there value =>
      .there (hostWireVarsAppend attachment right tail value)

private theorem hostWireVarsAppend_origin
    (attachment : ConcreteSpliceAttachment removed fragment)
    (right : List removed.complement.val.WireId) :
    ∀ (left : List removed.complement.val.WireId)
      {sig}
      (value :
        Var
          ((left ++ right).map
            (fun wire => (removed.complement.val.wires wire).sig))
          sig),
      ConcreteElaboration.WireContext.origin attachment.diagram
          ((left.map attachment.hostWire) ++
            (right.map attachment.hostWire))
          (hostWireVarsAppend attachment right left value) =
        attachment.hostWire
          (ConcreteElaboration.WireContext.origin
            removed.complement.val (left ++ right) value) := by
  intro left
  induction left with
  | nil =>
      intro sig value
      exact hostWireVars_origin attachment right value
  | cons wire tail induction =>
      intro sig value
      cases value with
      | here =>
          simp only [hostWireVarsAppend,
            ConcreteElaboration.WireContext.origin]
          exact
            (origin_castVar attachment.diagram
              (attachment.hostWire wire ::
                tail.map attachment.hostWire ++
                  right.map attachment.hostWire)
              (attachment.diagram_wire_hostWire wire) .here).trans rfl
      | there rest =>
          exact induction rest

private theorem hostExtendEnvFor_comp
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (localIds outerIds : List removed.complement.val.WireId)
    (targetValues :
      ConcreteElaboration.WireValues pre
        ((localIds.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig)))
    (targetEnv :
      Env pre
        ((outerIds.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig))) :
    Env.comp
        (ConcreteElaboration.extendEnvironmentFor attachment.diagram
          (outerIds.map attachment.hostWire)
          (localIds.map attachment.hostWire)
          targetValues targetEnv)
        (hostWireVarsAppend attachment outerIds localIds) =
      ConcreteElaboration.extendEnvironmentFor
        removed.complement.val outerIds localIds
        (hostWireValuesToSource attachment localIds targetValues)
        (Env.comp targetEnv (hostWireVars attachment outerIds)) := by
  induction localIds with
  | nil =>
      cases targetValues
      rfl
  | cons wire tail induction =>
      cases targetValues with
      | cons head rest =>
          funext sig value
          cases value with
          | here =>
              change
                (ConcreteElaboration.extendEnvironmentFor
                    attachment.diagram
                    (outerIds.map attachment.hostWire)
                    (tail.map attachment.hostWire) rest targetEnv).extend
                    head
                    (removed.complement.val.wires wire).sig
                    (castVar
                      (attachment.diagram_wire_hostWire wire)
                      .here) =
                  (ConcreteElaboration.extendEnvironmentFor
                    removed.complement.val outerIds tail
                    (hostWireValuesToSource attachment tail rest)
                    (Env.comp targetEnv
                      (hostWireVars attachment outerIds))).extend
                    (@Eq.ndrec Sig
                      (attachment.diagram.wires
                        (attachment.hostWire wire)).sig
                      (fun localSig => pre.Domain localSig) head
                      (removed.complement.val.wires wire).sig
                      (attachment.diagram_wire_hostWire wire))
                    (removed.complement.val.wires wire).sig
                    .here
              exact
                extend_castVar_here
                  (attachment.diagram_wire_hostWire wire)
                  (ConcreteElaboration.extendEnvironmentFor
                    attachment.diagram
                      (outerIds.map attachment.hostWire)
                      (tail.map attachment.hostWire) rest targetEnv)
                  head
          | there value =>
              change
                Env.comp
                    (ConcreteElaboration.extendEnvironmentFor
                      attachment.diagram
                      (outerIds.map attachment.hostWire)
                      (tail.map attachment.hostWire) rest targetEnv)
                    (hostWireVarsAppend attachment outerIds tail)
                    sig value =
                  ConcreteElaboration.extendEnvironmentFor
                    removed.complement.val outerIds tail
                    (hostWireValuesToSource attachment tail rest)
                    (Env.comp targetEnv
                      (hostWireVars attachment outerIds))
                    sig value
              exact congrFun (congrFun (induction rest) sig) value

private theorem extendEnvironmentFor_comp_transport
    {pre : PreModel}
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId)
    {sourceCtx : List Sig}
    {left right : List diagram.WireId}
    (equality : left = right)
    (sigsEquality :
      ((left ++ outerIds).map
          fun wire => (diagram.wires wire).sig) =
        ((right ++ outerIds).map
          fun wire => (diagram.wires wire).sig))
    (values :
      ConcreteElaboration.WireValues pre
        (left.map fun wire => (diagram.wires wire).sig))
    (outerEnv :
      Env pre
        (outerIds.map fun wire => (diagram.wires wire).sig))
    (rho :
      WireRenaming sourceCtx
        ((right ++ outerIds).map
          fun wire => (diagram.wires wire).sig)) :
    Env.comp
        (ConcreteElaboration.extendEnvironmentFor diagram outerIds
          left values outerEnv)
        (sigsEquality.symm ▸ rho) =
      Env.comp
        (ConcreteElaboration.extendEnvironmentFor diagram outerIds
          right
          (congrArg
              (List.map fun wire => (diagram.wires wire).sig)
              equality ▸
            values)
          outerEnv)
        rho := by
  have same :
      sigsEquality =
        congrArg
          (fun localIds =>
            (localIds ++ outerIds).map
              fun wire => (diagram.wires wire).sig)
          equality :=
    Subsingleton.elim _ _
  rw [same]
  cases equality
  rfl

theorem hostRegionLocalSigs_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    (attachment.diagram.wiresAt
        (attachment.hostRegion region)).map
          (fun wire => (attachment.diagram.wires wire).sig) =
      (removed.complement.val.wiresAt region).map
        (fun wire => (removed.complement.val.wires wire).sig) := by
  rw [candidate_wiresAt_hostRegion_eq attachment region notSite]
  exact hostWireSigsEq attachment
    (removed.complement.val.wiresAt region)

private theorem hostWireContext_extend_eq
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    hostWireContext attachment (context.extend region) =
      (hostWireContext attachment context).extend
        (attachment.hostRegion region) := by
  apply congrArg ConcreteElaboration.WireContext.mk
  unfold hostWireContext ConcreteElaboration.WireContext.extend
  rw [List.map_append,
    candidate_wiresAt_hostRegion_eq attachment region notSite]
  rfl

private def hostExtendedTargetSigsEq
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    ((hostWireContext attachment context).extend
        (attachment.hostRegion region)).sigs =
      (((removed.complement.val.wiresAt region).map
          attachment.hostWire ++
          context.ids.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig)) := by
  unfold ConcreteElaboration.WireContext.sigs
    ConcreteElaboration.WireContext.extend hostWireContext
  rw [candidate_wiresAt_hostRegion_eq attachment region notSite]
  rfl

def hostExtendedRenaming
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    WireRenaming
      (context.extend region).sigs
      ((hostWireContext attachment context).extend
        (attachment.hostRegion region)).sigs :=
  (hostExtendedTargetSigsEq attachment context region notSite).symm ▸
    hostWireVarsAppend attachment context.ids
      (removed.complement.val.wiresAt region)

private theorem origin_cast_ids
    (diagram : ConcreteDiagram definitionCount)
    {left right : List diagram.WireId}
    (same : left = right)
    {sig}
    (value :
      Var (right.map (fun wire => (diagram.wires wire).sig)) sig) :
    ConcreteElaboration.WireContext.origin diagram left
        ((congrArg
            (List.map (fun wire => (diagram.wires wire).sig))
            same).symm ▸ value) =
      ConcreteElaboration.WireContext.origin diagram right value := by
  cases same
  rfl

private theorem cast_renaming_apply
    (same : target = target')
    (rho : WireRenaming source target')
    {sig} (value : Var source sig) :
    ((same.symm ▸ rho) value) =
      (same.symm ▸ rho value) := by
  cases same
  rfl

theorem hostExtendedRenaming_origin
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site)
    {sig}
    (value : Var (context.extend region).sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        ((hostWireContext attachment context).extend
          (attachment.hostRegion region)).ids
        (hostExtendedRenaming attachment context region notSite value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin removed.complement.val
          (context.extend region).ids value) := by
  let idsEq :
      ((hostWireContext attachment context).extend
          (attachment.hostRegion region)).ids =
        (removed.complement.val.wiresAt region).map
            attachment.hostWire ++
          context.ids.map attachment.hostWire := by
    unfold ConcreteElaboration.WireContext.extend hostWireContext
    rw [candidate_wiresAt_hostRegion_eq attachment region notSite]
    rfl
  let raw :
      WireRenaming
        (context.extend region).sigs
        (((removed.complement.val.wiresAt region).map
              attachment.hostWire ++
            context.ids.map attachment.hostWire).map
          (fun wire => (attachment.diagram.wires wire).sig)) :=
    hostWireVarsAppend attachment context.ids
      (removed.complement.val.wiresAt region)
  have castEq :
      ((hostExtendedTargetSigsEq attachment context region notSite).symm ▸
          raw) value =
        ((congrArg
            (List.map
              (fun wire => (attachment.diagram.wires wire).sig))
            idsEq).symm ▸
          raw) value := by
    have proofEq :
        (hostExtendedTargetSigsEq
          attachment context region notSite).symm =
          (congrArg
            (List.map
              (fun wire => (attachment.diagram.wires wire).sig))
            idsEq).symm :=
      Subsingleton.elim _ _
    cases proofEq
    rfl
  change
    ConcreteElaboration.WireContext.origin attachment.diagram
        ((hostWireContext attachment context).extend
          (attachment.hostRegion region)).ids
        (((hostExtendedTargetSigsEq
          attachment context region notSite).symm ▸ raw) value) =
      _
  rw [castEq]
  have castApply :
      (((congrArg
          (List.map
            (fun wire => (attachment.diagram.wires wire).sig))
          idsEq).symm ▸ raw) value) =
        ((congrArg
            (List.map
              (fun wire => (attachment.diagram.wires wire).sig))
            idsEq).symm ▸ raw value) :=
    cast_renaming_apply
      (congrArg
        (List.map
          (fun wire => (attachment.diagram.wires wire).sig))
        idsEq)
      raw value
  rw [castApply]
  exact
    (origin_cast_ids attachment.diagram idsEq
      (raw value)).trans
      (hostWireVarsAppend_origin attachment context.ids
        (removed.complement.val.wiresAt region) value)

theorem hostExtendedRenaming_extendEnvironment
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site)
    (targetValues :
      ConcreteElaboration.WireValues pre
        ((attachment.diagram.wiresAt
          (attachment.hostRegion region)).map
            (fun wire => (attachment.diagram.wires wire).sig)))
    (targetEnv :
      Env pre (hostWireContext attachment context).sigs) :
    Env.comp
        (ConcreteElaboration.extendEnvironment attachment.diagram
          (hostWireContext attachment context)
          (attachment.hostRegion region)
          targetValues
          targetEnv)
        (hostExtendedRenaming attachment context region notSite) =
      ConcreteElaboration.extendEnvironment removed.complement.val
        context region
        (hostWireValuesToSource attachment
          (removed.complement.val.wiresAt region)
          (congrArg
              (List.map
                (fun wire =>
                  (attachment.diagram.wires wire).sig))
              (candidate_wiresAt_hostRegion_eq attachment region
                notSite) ▸
            targetValues))
        (Env.comp targetEnv
          (hostWireContextRenaming attachment context)) := by
  unfold ConcreteElaboration.extendEnvironment
  unfold hostExtendedRenaming
  simp only [hostWireContext,
    ConcreteElaboration.WireContext.sigs,
    ConcreteElaboration.WireContext.extend]
  let sourceValues :
      ConcreteElaboration.WireValues pre
        (((removed.complement.val.wiresAt region).map
          attachment.hostWire).map
            (fun wire => (attachment.diagram.wires wire).sig)) :=
    congrArg
        (List.map
          (fun wire => (attachment.diagram.wires wire).sig))
        (candidate_wiresAt_hostRegion_eq attachment region notSite) ▸
      targetValues
  have transport :=
    extendEnvironmentFor_comp_transport attachment.diagram
      (context.ids.map attachment.hostWire)
      (candidate_wiresAt_hostRegion_eq attachment region notSite)
      (hostExtendedTargetSigsEq
        attachment context region notSite)
      targetValues targetEnv
      (hostWireVarsAppend attachment context.ids
        (removed.complement.val.wiresAt region))
  have sourceFrame :=
    hostExtendEnvFor_comp attachment
      (removed.complement.val.wiresAt region) context.ids
      sourceValues targetEnv
  exact Eq.trans
    (by simpa only [sourceValues] using transport)
    (by
      simpa only [sourceValues, hostWireContextRenaming] using
        sourceFrame)

theorem hostWireContextRenaming_origin
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val)
    {sig : Sig} (value : Var context.sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (hostWireContext attachment context).ids
        (hostWireContextRenaming attachment context value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin
          removed.complement.val context.ids value) := by
  unfold hostWireContextRenaming
  unfold hostWireContext
  unfold ConcreteElaboration.WireContext.sigs
  exact hostWireVars_origin attachment context.ids value

theorem hostWireContext_nodup
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val)
    (nodup : context.ids.Nodup) :
    (hostWireContext attachment context).ids.Nodup := by
  unfold hostWireContext
  exact nodup.map attachment.hostWire (by
    intro left right different same
    exact different (attachment.hostWire_injective same))

private theorem hostWireContext_above
    (attachment : ConcreteSpliceAttachment removed fragment)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (sourceAbove :
      ConcreteElaboration.ContextAbove removed.complement.val
        sourceContext region) :
    ConcreteElaboration.ContextAbove attachment.diagram
      (hostWireContext attachment sourceContext)
      (attachment.hostRegion region) := by
  refine
    ⟨hostWireContext_nodup attachment sourceContext sourceAbove.1, ?_⟩
  intro targetWire targetMember
  obtain ⟨sourceWire, sourceMember, targetEquality⟩ :=
    List.mem_map.mp targetMember
  subst targetWire
  obtain ⟨steps, positive, climbed⟩ :=
    sourceAbove.2 sourceWire sourceMember
  refine ⟨steps, positive, ?_⟩
  rw [hostRegion_climb attachment, climbed,
    attachment.diagram_wire_hostWire_scope]
  rfl

private theorem hostEndpoint_incident
    (attachment : ConcreteSpliceAttachment removed fragment)
    (node : removed.complement.val.NodeId)
    (port : CPort)
    (wire : removed.complement.val.WireId)
    (incident :
      (⟨node, port⟩ :
        CEndpoint removed.complement.val.nodeCount) ∈
          (removed.complement.val.wires wire).endpoints) :
    (⟨attachment.hostNode node, port⟩ :
        CEndpoint attachment.diagram.nodeCount) ∈
      (attachment.diagram.wires
        (attachment.hostWire wire)).endpoints := by
  unfold ConcreteSpliceAttachment.diagram
    ConcreteSpliceAttachment.wireTable
    ConcreteSpliceAttachment.hostWire
  simp only [Fin.addCases_left]
  apply List.mem_append_left
  exact List.mem_map.mpr
    ⟨⟨node, port⟩, incident, rfl⟩

private theorem ItemSeq.renameWires_append
    (rho : WireRenaming source target) :
    ∀ (left right : ItemSeq definitions source),
      (left.append right).renameWires rho =
        (left.renameWires rho).append (right.renameWires rho)
  | .nil, _ => rfl
  | .cons head tail, right =>
      congrArg (ItemSeq.cons (head.renameWires rho))
        (ItemSeq.renameWires_append rho tail right)

private theorem compileNodes?_cons_eq_singleton_bind
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (node :: nodes) =
      (do
        let headItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context [node]
        let tailItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context nodes
        pure (headItems.append tailItems)) := by
  simp [ConcreteElaboration.compileNodes?, ItemSeq.append,
    Option.bind_assoc]

private theorem compileNodes?_cons_split
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          (node :: nodes) =
        some items) :
    ∃ headItems tailItems,
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
          some headItems ∧
        ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some tailItems ∧
        items = headItems.append tailItems := by
  rw [compileNodes?_cons_eq_singleton_bind] at compiled
  change
    (ConcreteElaboration.compileNodes? definitions diagram context
        [node]).bind (fun headItems =>
      (ConcreteElaboration.compileNodes? definitions diagram context
        nodes).bind (fun tailItems =>
          some (headItems.append tailItems))) =
      some items at compiled
  obtain ⟨headItems, headCompiled, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  obtain ⟨tailItems, tailCompiled, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have itemsEquality :
      headItems.append tailItems = items :=
    Option.some.inj compiled
  subst items
  exact ⟨headItems, tailItems, headCompiled, tailCompiled, rfl⟩

/--
Any ordered list of retained host nodes compiles naturally into the exact
host-wire context image.
-/
theorem compileHostNodes_natural
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed : attachment.diagram.WellFormed definitions)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (sourceNodup : sourceContext.ids.Nodup) :
    ∀ (nodes : List removed.complement.val.NodeId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileNodes? definitions removed.complement.val
          sourceContext nodes =
        some sourceItems →
      ∃ targetItems :
          ItemSeq definitions (hostWireContext attachment sourceContext).sigs,
        ConcreteElaboration.compileNodes? definitions attachment.diagram
            (hostWireContext attachment sourceContext)
            (nodes.map attachment.hostNode) =
          some targetItems ∧
        targetItems =
          sourceItems.renameWires
            (hostWireContextRenaming attachment sourceContext) := by
  intro nodes
  induction nodes with
  | nil =>
      intro sourceItems sourceCompiled
      have sourceEquality :
          (ItemSeq.nil :
            ItemSeq definitions sourceContext.sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using sourceCompiled)
      subst sourceItems
      exact ⟨.nil, by
        simp [ConcreteElaboration.compileNodes?], rfl⟩
  | cons node tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨headItems, tailItems, headCompiled,
          tailCompiled, sourceEquality⟩ :=
        compileNodes?_cons_split definitions removed.complement.val
          sourceContext node tail sourceItems sourceCompiled
      obtain ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        ConcreteElaboration.compileNodes?_singleton_natural
          candidateWellFormed
          (hostWireContext_nodup attachment sourceContext sourceNodup)
          (hostWireContextRenaming attachment sourceContext)
          attachment.hostWire
          attachment.diagram_wire_hostWire
          (hostWireContextRenaming_origin attachment sourceContext)
          attachment.hostRegion
          node (attachment.hostNode node)
          (by
            rw [ConcreteSpliceAttachment.diagram_node_hostNode]
            unfold ConcreteSpliceAttachment.renameHostNode
            cases removed.complement.val.nodes node <;> rfl)
          (by
            intro port wire incident
            exact hostEndpoint_incident attachment node port wire incident)
          headCompiled
      obtain ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine ⟨targetHead.append targetTail, ?_, ?_⟩
      · rw [List.map_cons, compileNodes?_cons_eq_singleton_bind]
        simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality, ItemSeq.renameWires_append,
          ← targetHeadEquality, ← targetTailEquality]

private theorem compileHostNodes_natural_generic
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed : attachment.diagram.WellFormed definitions)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (targetNodup : targetContext.ids.Nodup)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin
              removed.complement.val sourceContext.ids value)) :
    ∀ (nodes : List removed.complement.val.NodeId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileNodes? definitions removed.complement.val
          sourceContext nodes =
        some sourceItems →
      ∃ targetItems : ItemSeq definitions targetContext.sigs,
        ConcreteElaboration.compileNodes? definitions attachment.diagram
            targetContext (nodes.map attachment.hostNode) =
          some targetItems ∧
        targetItems = sourceItems.renameWires rho := by
  intro nodes
  induction nodes with
  | nil =>
      intro sourceItems sourceCompiled
      have sourceEquality :
          (ItemSeq.nil : ItemSeq definitions sourceContext.sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using sourceCompiled)
      subst sourceItems
      exact ⟨.nil, by simp [ConcreteElaboration.compileNodes?], rfl⟩
  | cons node tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨headItems, tailItems, headCompiled,
          tailCompiled, sourceEquality⟩ :=
        compileNodes?_cons_split definitions removed.complement.val
          sourceContext node tail sourceItems sourceCompiled
      obtain ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        ConcreteElaboration.compileNodes?_singleton_natural
          candidateWellFormed targetNodup rho attachment.hostWire
          attachment.diagram_wire_hostWire contextAction
          attachment.hostRegion node (attachment.hostNode node)
          (by
            rw [ConcreteSpliceAttachment.diagram_node_hostNode]
            unfold ConcreteSpliceAttachment.renameHostNode
            cases removed.complement.val.nodes node <;> rfl)
          (by
            intro port wire incident
            exact hostEndpoint_incident attachment node port wire incident)
          headCompiled
      obtain ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine ⟨targetHead.append targetTail, ?_, ?_⟩
      · rw [List.map_cons, compileNodes?_cons_eq_singleton_bind]
        simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality, ItemSeq.renameWires_append,
          ← targetHeadEquality, ← targetTailEquality]

theorem compileHostNodes_extended_natural
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed : attachment.diagram.WellFormed definitions)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site)
    (sourceNodup : (sourceContext.extend region).ids.Nodup)
    (nodes : List removed.complement.val.NodeId)
    {sourceItems :
      ItemSeq definitions (sourceContext.extend region).sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions removed.complement.val
          (sourceContext.extend region) nodes =
        some sourceItems) :
    ∃ targetItems :
        ItemSeq definitions
          ((hostWireContext attachment sourceContext).extend
            (attachment.hostRegion region)).sigs,
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          ((hostWireContext attachment sourceContext).extend
            (attachment.hostRegion region))
          (nodes.map attachment.hostNode) =
        some targetItems ∧
      targetItems =
        sourceItems.renameWires
          (hostExtendedRenaming attachment sourceContext region notSite) := by
  have targetNodup :
      ((hostWireContext attachment sourceContext).extend
        (attachment.hostRegion region)).ids.Nodup := by
    have mapped :=
      hostWireContext_nodup attachment (sourceContext.extend region)
        sourceNodup
    rw [hostWireContext_extend_eq attachment sourceContext region notSite]
      at mapped
    exact mapped
  exact
    compileHostNodes_natural_generic attachment candidateWellFormed
      (sourceContext.extend region)
      ((hostWireContext attachment sourceContext).extend
        (attachment.hostRegion region))
      targetNodup
      (hostExtendedRenaming attachment sourceContext region notSite)
      (hostExtendedRenaming_origin attachment sourceContext region notSite)
      nodes sourceCompiled

private theorem climb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) :
    diagram.climb (steps + 1) diagram.root = none := by
  have rootData : diagram.regions diagram.root = .sheet :=
    wellFormed.root_is_sheet
  simp [ConcreteDiagram.climb, rootData]

theorem climb_to_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          rw [climb_succ_root_none definitions diagram wellFormed right]
            at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          rw [climb_succ_root_none definitions diagram wellFormed left]
            at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet =>
              simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              have leftParent :
                  diagram.climb left parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using leftClimb
              have rightParent :
                  diagram.climb right parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using rightClimb
              exact congrArg Nat.succ
                (induction leftParent rightParent)

theorem climb_add
    (diagram : ConcreteDiagram definitionCount)
    (first second : Nat)
    (region : diagram.RegionId) :
    diagram.climb (first + second) region =
      (diagram.climb first region).bind (diagram.climb second) := by
  induction first generalizing region with
  | zero => simp
  | succ first induction =>
      cases regionData : diagram.regions region with
      | sheet =>
          simp [Nat.succ_add, ConcreteDiagram.climb, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, regionData, Nat.succ_add] using
            induction parent

theorem reaches_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (region : diagram.RegionId) :
    ∃ steps : Fin (diagram.regionCount + 1),
      diagram.climb steps region = some diagram.root := by
  have checked :=
    (List.all_eq_true.mp wellFormed.all_regions_reach_root)
      region (Data.Finite.mem_allFin region)
  exact
    (ConcreteElaboration.encloses_iff_exists
      diagram diagram.root region).mp (of_decide_eq_true checked)

private theorem climb_some_bound
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {ancestor descendant : diagram.RegionId}
    {steps : Nat}
    (climbed : diagram.climb steps descendant = some ancestor) :
    steps < diagram.regionCount + 1 := by
  obtain ⟨rootSteps, ancestorRoot⟩ :=
    reaches_root definitions diagram wellFormed ancestor
  have descendantRoot :
      diagram.climb (steps + rootSteps.val) descendant =
        some diagram.root := by
    rw [climb_add diagram steps rootSteps.val descendant, climbed]
    exact ancestorRoot
  obtain ⟨canonicalSteps, canonicalRoot⟩ :=
    reaches_root definitions diagram wellFormed descendant
  have sameDepth :=
    climb_to_root_unique definitions diagram wellFormed
      descendantRoot canonicalRoot
  omega

/-- Host-region enclosure is exactly the checked complement enclosure. -/
theorem hostRegion_encloses_iff
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    {ancestor descendant : removed.complement.val.RegionId} :
    attachment.diagram.Encloses
        (attachment.hostRegion ancestor)
        (attachment.hostRegion descendant) ↔
      removed.complement.val.Encloses ancestor descendant := by
  constructor
  · intro targetEncloses
    obtain ⟨⟨steps, _⟩, targetClimb⟩ :=
      (ConcreteElaboration.encloses_iff_exists
        attachment.diagram _ _).mp targetEncloses
    have mappedClimb :=
      hostRegion_climb attachment steps descendant
    rw [targetClimb] at mappedClimb
    cases sourceClimb :
        removed.complement.val.climb steps descendant with
    | none =>
        simp [sourceClimb] at mappedClimb
    | some reached =>
        have sameMapped :
            attachment.hostRegion ancestor =
              attachment.hostRegion reached := by
          have sameSome :
              some (attachment.hostRegion ancestor) =
                some (attachment.hostRegion reached) := by
            simpa only [sourceClimb, Option.map_some] using mappedClimb
          exact Option.some.inj sameSome
        have same : reached = ancestor :=
          hostRegion_injective attachment sameMapped.symm
        subst reached
        apply
          (ConcreteElaboration.encloses_iff_exists
            removed.complement.val ancestor descendant).mpr
        exact
          ⟨⟨steps,
            climb_some_bound definitions removed.complement.val
              removed.complement.property sourceClimb⟩,
            sourceClimb⟩
  · intro sourceEncloses
    obtain ⟨⟨steps, _⟩, sourceClimb⟩ :=
      (ConcreteElaboration.encloses_iff_exists
        removed.complement.val ancestor descendant).mp sourceEncloses
    apply
      (ConcreteElaboration.encloses_iff_exists
        attachment.diagram _ _).mpr
    refine ⟨⟨steps, ?_⟩, ?_⟩
    · simp only [ConcreteSpliceAttachment.diagram,
        ConcreteSpliceAttachment.regionCount]
      omega
    · rw [hostRegion_climb attachment, sourceClimb]
      rfl

theorem find_path_child
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    (attachment.diagram.childrenOf
        (attachment.hostRegion region)).find?
          (fun candidate =>
            decide
              (attachment.diagram.Encloses candidate
                (attachment.hostRegion removed.site))) =
      Option.map attachment.hostRegion
        ((removed.complement.val.childrenOf region).find?
          (fun candidate =>
            decide
              (removed.complement.val.Encloses candidate removed.site))) := by
  rw [candidate_childrenOf_hostRegion_eq attachment region notSite]
  let targetPredicate : attachment.diagram.RegionId → Bool :=
    fun candidate =>
      decide
        (attachment.diagram.Encloses candidate
          (attachment.hostRegion removed.site))
  let sourcePredicate : removed.complement.val.RegionId → Bool :=
    fun candidate =>
      decide
        (removed.complement.val.Encloses candidate removed.site)
  calc
    List.find? targetPredicate
        (List.map attachment.hostRegion
          (removed.complement.val.childrenOf region)) =
      Option.map attachment.hostRegion
        (List.find? (targetPredicate ∘ attachment.hostRegion)
          (removed.complement.val.childrenOf region)) :=
      List.find?_map
    _ =
      Option.map attachment.hostRegion
        (List.find? sourcePredicate
          (removed.complement.val.childrenOf region)) := by
      have predicates :
          targetPredicate ∘ attachment.hostRegion =
            sourcePredicate := by
        funext child
        simp only [Function.comp_apply]
        apply Bool.eq_iff_iff.mpr
        unfold targetPredicate sourcePredicate
        simp only [decide_eq_true_eq]
        exact hostRegion_encloses_iff attachment
      rw [predicates]

/-- Checked bounded enclosure is transitive. -/
theorem checked_encloses_trans
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {outer middle inner : diagram.RegionId}
    (outerMiddle : diagram.Encloses outer middle)
    (middleInner : diagram.Encloses middle inner) :
    diagram.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram outer middle).mp outerMiddle
  obtain ⟨middleSteps, middleClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram middle inner).mp middleInner
  obtain ⟨rootSteps, outerRoot⟩ :=
    reaches_root definitions diagram wellFormed outer
  have composed :
      diagram.climb (middleSteps.val + outerSteps.val) inner =
        some outer := by
    rw [climb_add diagram middleSteps.val outerSteps.val inner,
      middleClimb]
    exact outerClimb
  have composedRoot :
      diagram.climb
          ((middleSteps.val + outerSteps.val) + rootSteps.val)
          inner =
        some diagram.root := by
    rw [climb_add diagram
      (middleSteps.val + outerSteps.val) rootSteps.val inner,
      composed]
    exact outerRoot
  obtain ⟨canonicalRootSteps, canonicalRoot⟩ :=
    reaches_root definitions diagram wellFormed inner
  have sameDepth :=
    climb_to_root_unique definitions diagram wellFormed
      composedRoot canonicalRoot
  have composedBound :
      middleSteps.val + outerSteps.val < diagram.regionCount + 1 := by
    omega
  exact
    (ConcreteElaboration.encloses_iff_exists diagram outer inner).mpr
      ⟨⟨middleSteps.val + outerSteps.val, composedBound⟩, composed⟩

theorem parent_encloses_child
    (diagram : ConcreteDiagram definitionCount)
    (child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent) :
    diagram.Encloses parent child := by
  apply
    (ConcreteElaboration.encloses_iff_exists
      diagram parent child).mpr
  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, childData]

private theorem child_outside_of_parent_outside
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {parent child site : diagram.RegionId}
    (parentOutside : ¬diagram.Encloses parent site)
    (childData : diagram.regions child = .cut parent) :
    ¬diagram.Encloses child site := by
  intro childEncloses
  exact parentOutside
    (checked_encloses_trans definitions diagram wellFormed
      (parent_encloses_child diagram child parent childData)
      childEncloses)

theorem hostWireContext_extend
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (context :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site) :
    hostWireContext attachment (context.extend region) =
      (hostWireContext attachment context).extend
        (attachment.hostRegion region) := by
  exact hostWireContext_extend_eq attachment context region notSite

private theorem child_data_of_mem
    (diagram : ConcreteDiagram definitionCount)
    (parent child : diagram.RegionId)
    (member : child ∈ diagram.childrenOf parent) :
    diagram.regions child = .cut parent :=
  ConcreteElaboration.mem_childrenOf diagram parent child member

private theorem origin_mem
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => simp [ConcreteElaboration.WireContext.origin]
      | there rest =>
          exact List.mem_cons_of_mem head (induction rest)

theorem origin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    {sig : Sig}
    {left right :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig}
    (same :
      ConcreteElaboration.WireContext.origin diagram ids left =
        ConcreteElaboration.WireContext.origin diagram ids right) :
    left = right := by
  induction ids with
  | nil => nomatch left
  | cons head tail induction =>
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there right =>
              have rightMember := origin_mem diagram tail right
              have headNotTail := (List.nodup_cons.mp nodup).1
              have equality :
                  head =
                    ConcreteElaboration.WireContext.origin
                      diagram tail right := by
                simpa [ConcreteElaboration.WireContext.origin] using same
              rw [← equality] at rightMember
              exact False.elim (headNotTail rightMember)
      | there left =>
          cases right with
          | here =>
              have leftMember := origin_mem diagram tail left
              have headNotTail := (List.nodup_cons.mp nodup).1
              have equality :
                  ConcreteElaboration.WireContext.origin
                      diagram tail left =
                    head := by
                simpa [ConcreteElaboration.WireContext.origin] using same
              rw [equality] at leftMember
              exact False.elim (headNotTail leftMember)
          | there right =>
              exact congrArg Var.there
                (induction (List.nodup_cons.mp nodup).2
                  (by simpa [ConcreteElaboration.WireContext.origin]
                    using same))

def hostContextRenamingThrough
    (attachment : ConcreteSpliceAttachment removed fragment)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (same : hostWireContext attachment sourceContext = targetContext) :
    WireRenaming sourceContext.sigs targetContext.sigs :=
  congrArg ConcreteElaboration.WireContext.sigs same ▸
    hostWireContextRenaming attachment sourceContext

theorem hostContextRenamingThrough_origin
    (attachment : ConcreteSpliceAttachment removed fragment)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (same : hostWireContext attachment sourceContext = targetContext)
    {sig}
    (value : Var sourceContext.sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        targetContext.ids
        (hostContextRenamingThrough attachment sourceContext
          targetContext same value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin removed.complement.val
          sourceContext.ids value) := by
  cases same
  simpa [hostContextRenamingThrough] using
    hostWireContextRenaming_origin attachment sourceContext value

theorem hostContextRenamingThrough_extend_eq
    (attachment : ConcreteSpliceAttachment removed fragment)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (region : removed.complement.val.RegionId)
    (notSite : region ≠ removed.site)
    (sourceNodup : (sourceContext.extend region).ids.Nodup) :
    (fun {sig} value =>
      hostContextRenamingThrough attachment
        (sourceContext.extend region)
        ((hostWireContext attachment sourceContext).extend
          (attachment.hostRegion region))
        (hostWireContext_extend_eq attachment sourceContext region
          notSite) (sig := sig) value) =
      (fun {sig} value =>
        hostExtendedRenaming attachment sourceContext region notSite
          (sig := sig) value) := by
  funext sig value
  have targetNodup :
      ((hostWireContext attachment sourceContext).extend
        (attachment.hostRegion region)).ids.Nodup := by
    have mapped :=
      hostWireContext_nodup attachment (sourceContext.extend region)
        sourceNodup
    rw [hostWireContext_extend_eq attachment sourceContext region notSite]
      at mapped
    exact mapped
  apply origin_injective attachment.diagram
    ((hostWireContext attachment sourceContext).extend
      (attachment.hostRegion region)).ids targetNodup
  rw [hostContextRenamingThrough_origin,
    hostExtendedRenaming_origin]

theorem hostContextRenamingThrough_self_eq
    (attachment : ConcreteSpliceAttachment removed fragment)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val)
    (same :
      hostWireContext attachment sourceContext =
        hostWireContext attachment sourceContext)
    (sourceNodup : sourceContext.ids.Nodup) :
    (fun {sig} value =>
      hostContextRenamingThrough attachment sourceContext
        (hostWireContext attachment sourceContext) same
        (sig := sig) value) =
      (fun {sig} value =>
        hostWireContextRenaming attachment sourceContext
          (sig := sig) value) := by
  funext sig value
  apply origin_injective attachment.diagram
    (hostWireContext attachment sourceContext).ids
    (hostWireContext_nodup attachment sourceContext sourceNodup)
  rw [hostContextRenamingThrough_origin,
    hostWireContextRenaming_origin]

theorem compileRegion_host_denotation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed :
      attachment.diagram.WellFormed definitions)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∀ (sourceFuel targetFuel : Nat)
      (region : removed.complement.val.RegionId)
      (sourceContext :
        ConcreteElaboration.WireContext removed.complement.val)
      (targetContext :
        ConcreteElaboration.WireContext attachment.diagram)
      (contexts :
        hostWireContext attachment sourceContext = targetContext)
      {sourceBody :
        Region definitions sourceContext.sigs}
      {targetBody :
        Region definitions targetContext.sigs},
      (outside :
        ¬removed.complement.val.Encloses region removed.site) →
      (sourceAbove :
        ConcreteElaboration.ContextAbove removed.complement.val
          sourceContext region) →
      ConcreteElaboration.compileRegion? definitions
          removed.complement.val sourceFuel region sourceContext =
        some sourceBody →
      ConcreteElaboration.compileRegion? definitions
          attachment.diagram targetFuel
          (attachment.hostRegion region)
          targetContext =
        some targetBody →
      ∀ targetEnv :
          Env pre targetContext.sigs,
        denoteRegion pre definitionEnv targetEnv targetBody ↔
          denoteRegion pre definitionEnv
            (Env.comp targetEnv
              (hostContextRenamingThrough attachment sourceContext
                targetContext contexts))
            sourceBody := by
  intro sourceFuel
  induction sourceFuel with
  | zero =>
      intro targetFuel region sourceContext targetContext contexts sourceBody
        targetBody outside sourceAbove sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ sourceFuel induction =>
      intro targetFuel
      cases targetFuel with
      | zero =>
          intro region sourceContext targetContext contexts sourceBody
            targetBody outside sourceAbove sourceCompiled targetCompiled
          simp [ConcreteElaboration.compileRegion?] at targetCompiled
      | succ targetFuel =>
          intro region sourceContext targetContext contexts sourceBody
            targetBody outside sourceAbove sourceCompiled targetCompiled
            targetEnv
          let outerContexts := contexts
          subst targetContext
          have notSite : region ≠ removed.site := by
            intro same
            subst region
            exact outside
              (ConcreteDiagram.encloses_refl
                removed.complement.val removed.site)
          simp only [ConcreteElaboration.compileRegion?] at sourceCompiled
          simp only [ConcreteElaboration.compileRegion?] at targetCompiled
          cases sourceNodesEquation :
              ConcreteElaboration.compileNodes? definitions
                removed.complement.val (sourceContext.extend region)
                (removed.complement.val.nodesAt region) with
          | none =>
              rw [sourceNodesEquation] at sourceCompiled
              simp at sourceCompiled
          | some sourceNodes =>
              rw [sourceNodesEquation] at sourceCompiled
              cases sourceChildrenEquation :
                  ConcreteElaboration.compileChildrenWith? definitions
                    removed.complement.val
                    (ConcreteElaboration.compileRegion? definitions
                      removed.complement.val sourceFuel)
                    (sourceContext.extend region)
                    (removed.complement.val.childrenOf region) with
              | none =>
                  rw [sourceChildrenEquation] at sourceCompiled
                  simp at sourceCompiled
              | some sourceChildren =>
                  rw [sourceChildrenEquation] at sourceCompiled
                  cases targetNodesEquation :
                      ConcreteElaboration.compileNodes? definitions
                        attachment.diagram
                        ((hostWireContext attachment sourceContext).extend
                          (attachment.hostRegion region))
                        (attachment.diagram.nodesAt
                          (attachment.hostRegion region)) with
                  | none =>
                      rw [targetNodesEquation] at targetCompiled
                      simp at targetCompiled
                  | some targetNodes =>
                      rw [targetNodesEquation] at targetCompiled
                      cases targetChildrenEquation :
                          ConcreteElaboration.compileChildrenWith? definitions
                            attachment.diagram
                            (ConcreteElaboration.compileRegion? definitions
                              attachment.diagram targetFuel)
                            ((hostWireContext attachment sourceContext).extend
                              (attachment.hostRegion region))
                            (attachment.diagram.childrenOf
                              (attachment.hostRegion region)) with
                      | none =>
                          rw [targetChildrenEquation] at targetCompiled
                          simp at targetCompiled
                      | some targetChildren =>
                          rw [targetChildrenEquation] at targetCompiled
                          have sourceBodyEquality :
                              ConcreteElaboration.finishRegion
                                  removed.complement.val sourceContext region
                                  (.mk
                                    (sourceNodes.append sourceChildren)) =
                                sourceBody :=
                            Option.some.inj sourceCompiled
                          have targetBodyEquality :
                              ConcreteElaboration.finishRegion
                                  attachment.diagram
                                  (hostWireContext attachment sourceContext)
                                  (attachment.hostRegion region)
                                  (.mk
                                    (targetNodes.append targetChildren)) =
                                targetBody :=
                            Option.some.inj targetCompiled
                          subst sourceBody
                          subst targetBody
                          rw [candidate_nodesAt_hostRegion_eq
                            attachment region notSite] at targetNodesEquation
                          rw [candidate_childrenOf_hostRegion_eq
                            attachment region notSite] at targetChildrenEquation
                          have sourceExtendedNodup :
                              (sourceContext.extend region).ids.Nodup :=
                            ConcreteElaboration.extend_nodup definitions
                              removed.complement.val
                              removed.complement.property sourceContext region
                              sourceAbove
                          obtain ⟨naturalTargetNodes,
                              naturalTargetNodesCompiled,
                              naturalTargetNodesEquality⟩ :=
                            compileHostNodes_extended_natural attachment
                              candidateWellFormed sourceContext region notSite
                              sourceExtendedNodup
                              (removed.complement.val.nodesAt region)
                              sourceNodesEquation
                          have targetNodesEquality :
                              targetNodes =
                                sourceNodes.renameWires
                                  (hostExtendedRenaming attachment
                                    sourceContext region notSite) := by
                            have storedEquality :
                                naturalTargetNodes = targetNodes :=
                              Option.some.inj
                                (naturalTargetNodesCompiled.symm.trans
                                  targetNodesEquation)
                            exact storedEquality.symm.trans
                              naturalTargetNodesEquality
                          have extendedRenamingEquality :=
                            hostContextRenamingThrough_extend_eq attachment
                              sourceContext region notSite sourceExtendedNodup
                          have childrenNatural
                              (targetExtendedEnv :
                                Env pre
                                  ((hostWireContext attachment
                                    sourceContext).extend
                                    (attachment.hostRegion region)).sigs) :
                              denoteItemSeq pre definitionEnv
                                  targetExtendedEnv targetChildren ↔
                                denoteItemSeq pre definitionEnv
                                  (Env.comp targetExtendedEnv
                                  (hostExtendedRenaming attachment
                                      sourceContext region notSite))
                                  sourceChildren := by
                            clear sourceCompiled targetCompiled
                            generalize childrenEquation :
                                removed.complement.val.childrenOf region =
                                  children
                            rw [childrenEquation] at sourceChildrenEquation targetChildrenEquation
                            have childrenOutside :
                                ∀ child, child ∈ children →
                                  ¬removed.complement.val.Encloses child
                                    removed.site := by
                              intro child member
                              apply child_outside_of_parent_outside definitions
                                removed.complement.val
                                removed.complement.property outside
                              apply child_data_of_mem
                                removed.complement.val region child
                              rw [childrenEquation]
                              exact member
                            have childrenAbove :
                                ∀ child, child ∈ children →
                                  ConcreteElaboration.ContextAbove
                                    removed.complement.val
                                    (sourceContext.extend region) child := by
                              intro child member
                              apply ConcreteElaboration.extend_above_child
                                definitions removed.complement.val
                                removed.complement.property sourceContext region
                                child sourceAbove
                              apply child_data_of_mem
                                removed.complement.val region child
                              rw [childrenEquation]
                              exact member
                            clear childrenEquation
                            induction children
                                generalizing sourceChildren targetChildren with
                            | nil =>
                                have sourceItemsEquality :
                                    (ItemSeq.nil :
                                      ItemSeq definitions
                                        (sourceContext.extend region).sigs) =
                                      sourceChildren :=
                                  Option.some.inj sourceChildrenEquation
                                have targetItemsEquality :
                                    (ItemSeq.nil :
                                      ItemSeq definitions
                                        ((hostWireContext attachment
                                          sourceContext).extend
                                          (attachment.hostRegion
                                            region)).sigs) =
                                      targetChildren :=
                                  Option.some.inj targetChildrenEquation
                                subst sourceChildren
                                subst targetChildren
                                rfl
                            | cons child tail childrenInduction =>
                                simp only
                                  [ConcreteElaboration.compileChildrenWith?,
                                    List.map_cons] at sourceChildrenEquation
                                simp only
                                  [ConcreteElaboration.compileChildrenWith?,
                                    List.map_cons] at targetChildrenEquation
                                cases sourceHeadEquation :
                                    ConcreteElaboration.compileRegion?
                                      definitions removed.complement.val
                                      sourceFuel child
                                      (sourceContext.extend region) with
                                | none =>
                                    simp [sourceHeadEquation] at sourceChildrenEquation
                                | some sourceHead =>
                                    rw [sourceHeadEquation] at sourceChildrenEquation
                                    cases sourceTailEquation :
                                        ConcreteElaboration.compileChildrenWith?
                                          definitions removed.complement.val
                                          (ConcreteElaboration.compileRegion?
                                            definitions
                                            removed.complement.val sourceFuel)
                                          (sourceContext.extend region)
                                          tail with
                                    | none =>
                                        simp [sourceTailEquation] at sourceChildrenEquation
                                    | some sourceTail =>
                                        rw [sourceTailEquation] at sourceChildrenEquation
                                        cases targetHeadEquation :
                                            ConcreteElaboration.compileRegion?
                                              definitions attachment.diagram
                                              targetFuel
                                              (attachment.hostRegion child)
                                              ((hostWireContext attachment
                                                sourceContext).extend
                                                (attachment.hostRegion
                                                  region)) with
                                        | none =>
                                            simp [targetHeadEquation] at targetChildrenEquation
                                        | some targetHead =>
                                            rw [targetHeadEquation] at targetChildrenEquation
                                            change
                                              (ConcreteElaboration.compileChildrenWith?
                                                definitions
                                                attachment.diagram
                                                (ConcreteElaboration.compileRegion?
                                                  definitions
                                                  attachment.diagram
                                                  targetFuel)
                                                ((hostWireContext attachment
                                                  sourceContext).extend
                                                  (attachment.hostRegion region))
                                                (tail.map
                                                  attachment.hostRegion)).bind
                                                  (fun targetTail =>
                                                    some
                                                      (ItemSeq.cons
                                                        (.cut targetHead)
                                                        targetTail)) =
                                                some targetChildren
                                              at targetChildrenEquation
                                            obtain ⟨targetTail,
                                                targetTailEquation,
                                                targetItemsEquation⟩ :=
                                              Option.bind_eq_some_iff.mp
                                                targetChildrenEquation
                                            have sourceItemsEquality :
                                                (ItemSeq.cons
                                                    (.cut sourceHead)
                                                    sourceTail :
                                                  ItemSeq definitions
                                                    (sourceContext.extend
                                                      region).sigs) =
                                                  sourceChildren :=
                                              Option.some.inj
                                                sourceChildrenEquation
                                            have targetItemsEquality :
                                                (ItemSeq.cons
                                                    (.cut targetHead)
                                                    targetTail :
                                                  ItemSeq definitions
                                                    ((hostWireContext
                                                      attachment
                                                      sourceContext).extend
                                                      (attachment.hostRegion
                                                        region)).sigs) =
                                                  targetChildren :=
                                              Option.some.inj
                                                targetItemsEquation
                                            subst sourceChildren
                                            subst targetChildren
                                            have headNatural :=
                                              induction targetFuel child
                                                (sourceContext.extend region)
                                                ((hostWireContext attachment
                                                  sourceContext).extend
                                                  (attachment.hostRegion
                                                    region))
                                                (hostWireContext_extend_eq
                                                  attachment sourceContext
                                                  region notSite)
                                                (childrenOutside child
                                                  (by simp))
                                                (childrenAbove child
                                                  (by simp))
                                                sourceHeadEquation
                                                targetHeadEquation
                                                targetExtendedEnv
                                            rw [extendedRenamingEquality]
                                              at headNatural
                                            have tailNatural :=
                                              childrenInduction
                                                sourceTail targetTail
                                                targetTailEquation
                                                sourceTailEquation
                                                (by
                                                  intro candidate member
                                                  exact childrenOutside
                                                    candidate
                                                    (by simp [member]))
                                                (by
                                                  intro candidate member
                                                  exact childrenAbove
                                                    candidate
                                                    (by simp [member]))
                                            exact
                                              and_congr
                                                (not_congr headNatural)
                                                tailNatural
                          have coreNatural
                              (targetExtendedEnv :
                                Env pre
                                  ((hostWireContext attachment
                                    sourceContext).extend
                                    (attachment.hostRegion region)).sigs) :
                              denoteItemSeq pre definitionEnv targetExtendedEnv
                                  (targetNodes.append targetChildren) ↔
                                denoteItemSeq pre definitionEnv
                                  (Env.comp targetExtendedEnv
                                    (hostExtendedRenaming attachment
                                      sourceContext region notSite))
                                  (sourceNodes.append sourceChildren) := by
                            rw [denoteItemSeq_append,
                              denoteItemSeq_append]
                            apply and_congr
                            · rw [targetNodesEquality,
                                denoteItemSeq_renameWires]
                            · exact childrenNatural targetExtendedEnv
                          have outerRenamingEquality :=
                            hostContextRenamingThrough_self_eq attachment
                              sourceContext outerContexts sourceAbove.1
                          rw [outerRenamingEquality]
                          rw [ConcreteElaboration.denote_finishRegion,
                            ConcreteElaboration.denote_finishRegion]
                          constructor
                          · rintro ⟨targetValues, targetCoreDenotes⟩
                            let sourceValues :=
                              hostWireValuesToSource attachment
                                (removed.complement.val.wiresAt region)
                                (congrArg
                                    (List.map
                                      (fun wire =>
                                        (attachment.diagram.wires wire).sig))
                                    (candidate_wiresAt_hostRegion_eq
                                      attachment region notSite) ▸
                                  targetValues)
                            refine ⟨sourceValues, ?_⟩
                            have environmentEquality :=
                              hostExtendedRenaming_extendEnvironment
                                attachment sourceContext region notSite
                                targetValues targetEnv
                            change
                              denoteItemSeq pre definitionEnv
                                (ConcreteElaboration.extendEnvironment
                                  removed.complement.val sourceContext region
                                  sourceValues
                                  (Env.comp targetEnv
                                    (hostWireContextRenaming attachment
                                      sourceContext)))
                                (sourceNodes.append sourceChildren)
                            rw [← environmentEquality]
                            exact
                              (coreNatural
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram
                                  (hostWireContext attachment sourceContext)
                                  (attachment.hostRegion region)
                                  targetValues targetEnv)).mp
                                targetCoreDenotes
                          · rintro ⟨sourceValues, sourceCoreDenotes⟩
                            let mappedTargetValues :=
                              hostWireValuesToTarget attachment
                                (removed.complement.val.wiresAt region)
                                sourceValues
                            let targetValues :
                                ConcreteElaboration.WireValues pre
                                  ((attachment.diagram.wiresAt
                                    (attachment.hostRegion region)).map
                                    (fun wire =>
                                      (attachment.diagram.wires wire).sig)) :=
                              (congrArg
                                (List.map
                                  (fun wire =>
                                    (attachment.diagram.wires wire).sig))
                                (candidate_wiresAt_hostRegion_eq attachment
                                  region notSite)).symm ▸ mappedTargetValues
                            refine ⟨targetValues, ?_⟩
                            have targetCastRoundTrip :
                                congrArg
                                    (List.map
                                      (fun wire =>
                                        (attachment.diagram.wires wire).sig))
                                    (candidate_wiresAt_hostRegion_eq attachment
                                      region notSite) ▸ targetValues =
                                  mappedTargetValues := by
                              unfold targetValues
                              exact wireValues_cast_cancel
                                (congrArg
                                  (List.map
                                    (fun wire =>
                                      (attachment.diagram.wires wire).sig))
                                  (candidate_wiresAt_hostRegion_eq attachment
                                    region notSite)).symm
                                mappedTargetValues
                            have sourceValuesRoundTrip :
                                hostWireValuesToSource attachment
                                    (removed.complement.val.wiresAt region)
                                    (congrArg
                                        (List.map
                                          (fun wire =>
                                            (attachment.diagram.wires
                                              wire).sig))
                                        (candidate_wiresAt_hostRegion_eq
                                          attachment region notSite) ▸
                                      targetValues) =
                                  sourceValues := by
                              rw [targetCastRoundTrip]
                              exact hostWireValues_target_source attachment
                                (removed.complement.val.wiresAt region)
                                sourceValues
                            have environmentEquality :=
                              hostExtendedRenaming_extendEnvironment
                                attachment sourceContext region notSite
                                targetValues targetEnv
                            rw [sourceValuesRoundTrip] at environmentEquality
                            change
                              denoteItemSeq pre definitionEnv
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram
                                  (hostWireContext attachment sourceContext)
                                  (attachment.hostRegion region)
                                  targetValues targetEnv)
                                (targetNodes.append targetChildren)
                            apply
                              (coreNatural
                                (ConcreteElaboration.extendEnvironment
                                  attachment.diagram
                                  (hostWireContext attachment sourceContext)
                                  (attachment.hostRegion region)
                                  targetValues targetEnv)).mpr
                            rw [environmentEquality]
                            exact sourceCoreDenotes

theorem compileChildren_host_denotation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (candidateWellFormed :
      attachment.diagram.WellFormed definitions)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceFuel targetFuel : Nat)
    (sourceContext :
      ConcreteElaboration.WireContext removed.complement.val) :
    ∀ (children : List removed.complement.val.RegionId)
      {sourceItems : ItemSeq definitions sourceContext.sigs}
      {targetItems :
        ItemSeq definitions
          (hostWireContext attachment sourceContext).sigs},
      (∀ child, child ∈ children →
        ¬removed.complement.val.Encloses child removed.site) →
      (∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove removed.complement.val
          sourceContext child) →
      ConcreteElaboration.compileChildrenWith? definitions
          removed.complement.val
          (ConcreteElaboration.compileRegion? definitions
            removed.complement.val sourceFuel)
          sourceContext children =
        some sourceItems →
      ConcreteElaboration.compileChildrenWith? definitions
          attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram targetFuel)
          (hostWireContext attachment sourceContext)
          (children.map attachment.hostRegion) =
        some targetItems →
      ∀ targetEnv :
          Env pre (hostWireContext attachment sourceContext).sigs,
        denoteItemSeq pre definitionEnv targetEnv targetItems ↔
          denoteItemSeq pre definitionEnv
            (targetEnv.comp
              (hostContextRenamingThrough attachment sourceContext
                (hostWireContext attachment sourceContext) rfl))
            sourceItems := by
  intro children
  induction children with
  | nil =>
      intro sourceItems targetItems _ _ sourceCompiled targetCompiled
        targetEnv
      have sourceEquality : (.nil : ItemSeq definitions sourceContext.sigs) =
          sourceItems :=
        Option.some.inj sourceCompiled
      have targetEquality :
          (.nil :
            ItemSeq definitions
              (hostWireContext attachment sourceContext).sigs) =
            targetItems :=
        Option.some.inj targetCompiled
      subst sourceItems
      subst targetItems
      rfl
  | cons child tail induction =>
      intro sourceItems targetItems allOutside allAbove sourceCompiled
        targetCompiled targetEnv
      simp only [ConcreteElaboration.compileChildrenWith?] at sourceCompiled targetCompiled
      obtain ⟨sourceHead, sourceHeadCompiled, sourceRestCompiled⟩ :=
        Option.bind_eq_some_iff.mp sourceCompiled
      obtain ⟨sourceTail, sourceTailCompiled, sourceItemsCompiled⟩ :=
        Option.bind_eq_some_iff.mp sourceRestCompiled
      obtain ⟨targetHead, targetHeadCompiled, targetRestCompiled⟩ :=
        Option.bind_eq_some_iff.mp targetCompiled
      obtain ⟨targetTail, targetTailCompiled, targetItemsCompiled⟩ :=
        Option.bind_eq_some_iff.mp targetRestCompiled
      have sourceItemsEquality :
          (ItemSeq.cons (.cut sourceHead) sourceTail :
            ItemSeq definitions sourceContext.sigs) = sourceItems :=
        Option.some.inj sourceItemsCompiled
      have targetItemsEquality :
          (ItemSeq.cons (.cut targetHead) targetTail :
            ItemSeq definitions
              (hostWireContext attachment sourceContext).sigs) =
            targetItems :=
        Option.some.inj targetItemsCompiled
      subst sourceItems
      subst targetItems
      have headNatural :=
        compileRegion_host_denotation attachment candidateWellFormed pre
          definitionEnv sourceFuel targetFuel child sourceContext
          (hostWireContext attachment sourceContext) rfl
          (allOutside child (by simp))
          (allAbove child (by simp))
          sourceHeadCompiled targetHeadCompiled targetEnv
      have tailNatural :=
        induction
          (by
            intro candidate member
            exact allOutside candidate (by simp [member]))
          (by
            intro candidate member
            exact allAbove candidate (by simp [member]))
          sourceTailCompiled targetTailCompiled targetEnv
      exact and_congr (not_congr headNatural) tailNatural

end RemovalFactorization

end VisualProof
