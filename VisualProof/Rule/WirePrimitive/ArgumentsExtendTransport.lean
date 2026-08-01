import VisualProof.Rule.WirePrimitive.Arguments

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

namespace AppliedArgExtend

/-- Coordinate in the larger vector corresponding to a coordinate after
deleting `position`. -/
private def restorePosition (position index : Nat) : Nat :=
  if index < position then index else index + 1

private theorem eraseAt_getElem?_restorePosition
    (values : List α) (position index : Nat)
    (positionValid : position < values.length)
    (indexBound : index + 1 < values.length) :
    values[restorePosition position index]? =
      (ConcreteWirePrimitive.eraseAt values position)[index]? := by
  induction values generalizing position index with
  | nil => simp at positionValid
  | cons head tail induction =>
      cases position with
      | zero =>
          cases index with
          | zero => rfl
          | succ index => simp [restorePosition,
              ConcreteWirePrimitive.eraseAt]
      | succ position =>
          cases index with
          | zero => simp [restorePosition, ConcreteWirePrimitive.eraseAt]
          | succ index =>
              simp only [List.length_cons, Nat.succ_lt_succ_iff]
                at positionValid
              have nextBound : index + 1 < tail.length := by
                simp only [List.length_cons, Nat.succ_add,
                  Nat.succ_lt_succ_iff] at indexBound
                exact indexBound
              by_cases before : index < position
              · simpa [restorePosition, ConcreteWirePrimitive.eraseAt,
                  before] using
                  induction position index positionValid nextBound
              · simpa [restorePosition, ConcreteWirePrimitive.eraseAt,
                  before] using
                  induction position index positionValid nextBound

private theorem insertAt_getElem?_restorePosition
    (values : List α) (position index : Nat) (value : α)
    (positionValid : position ≤ values.length)
    (indexBound : index < values.length) :
    (ConcreteWirePrimitive.insertAt values position value)[
        restorePosition position index]? = values[index]? := by
  induction values generalizing position index with
  | nil => simp at indexBound
  | cons head tail induction =>
      cases position with
      | zero => simp [restorePosition, ConcreteWirePrimitive.insertAt]
      | succ position =>
          cases index with
          | zero => simp [restorePosition, ConcreteWirePrimitive.insertAt]
          | succ index =>
              simp only [List.length_cons, Nat.succ_le_succ_iff]
                at positionValid
              simp only [List.length_cons, Nat.succ_lt_succ_iff]
                at indexBound
              by_cases before : index < position
              · simpa [restorePosition, ConcreteWirePrimitive.insertAt,
                  before] using
                  induction position index positionValid indexBound

              · simpa [restorePosition, ConcreteWirePrimitive.insertAt,
                  before] using
                  induction position index positionValid indexBound

private theorem insertAt_length_of_le
    (values : List α) (position : Nat) (value : α)
    (valid : position ≤ values.length) :
    (ConcreteWirePrimitive.insertAt values position value).length =
      values.length + 1 := by
  induction values generalizing position with
  | nil =>
      simp only [List.length_nil] at valid
      have positionZero : position = 0 := by omega
      subst position
      rfl
  | cons head tail induction =>
      cases position with
      | zero => simp [ConcreteWirePrimitive.insertAt]
      | succ position =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at valid
          simp [ConcreteWirePrimitive.insertAt, induction position valid]

theorem nodeEquiv_generated_mem
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied : AppliedArgExtend source orientation wire position newArgument
      attachments)
    (node : source.val.NodeId)
    (generated : node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.sourceSites) :
    applied.nodeEquiv node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.targetSites := by
  let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
    applied.sourceSites node generated
  have sourceExact : (applied.sourceSites.sites.get site).node = node :=
    ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
      applied.sourceSites node generated
  rw [← sourceExact]
  have image : applied.nodeEquiv
      (applied.sourceSites.sites.get site).node =
      applied.argumentResult.targetNode site := by
    simpa [AppliedArgExtend.sourceSites, AppliedArgExtend.argumentResult]
      using applied.nodeEquiv_generated site
  rw [image]
  exact applied.argumentResult.generatedNode_targetSiteNode
    applied.targetSites site

/-- The suffix isomorphism identifies the inverse drop's source argument
vector with the exact extension target vector. -/
theorem inverseSourceArguments_exact
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    backward.sourceArgumentList = forward.targetArgumentList := by
  have signatureExact := targetIso.wire_signature backwardWire
  have forwardSignature :
      (forward.target.val.wires forward.targetWire).sig =
        .rel forward.targetArgumentList :=
    forward.targetWire_signature
  rw [wireExact, forwardSignature, backward.sourceWire_signature]
    at signatureExact
  exact Sig.rel.inj signatureExact.symm

/-- Extension followed by its checked drop restores the planned argument
vector exactly. -/
theorem inverseTargetArguments_exact
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    backward.targetArgumentList = forward.sourceArgumentList := by
  calc
    backward.targetArgumentList =
        ConcreteWirePrimitive.eraseAt backward.sourceArgumentList position :=
      backward.targetArguments_exact
    _ = ConcreteWirePrimitive.eraseAt forward.targetArgumentList position := by
      rw [forward.inverseSourceArguments_exact backward targetIso wireExact]
    _ = forward.sourceArgumentList := forward.eraseTargetArguments_exact

/-- Region carrier of the transported extension/drop pair. -/
def inverseTransportRegionEquiv
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.RegionId planned.val.RegionId :=
  forward.argumentResult.inverseTransportRegionEquiv backward.argumentResult
    targetIso

/-- Node carrier of the transported extension/drop pair. -/
def inverseTransportNodeEquiv
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.NodeId planned.val.NodeId :=
  forward.argumentResult.inverseTransportNodeEquiv backward.argumentResult
    forward.targetSites backward.targetSites targetIso

/-- Exact head-only wire carrier of the transported extension/drop pair. -/
def inverseTransportWireEquiv
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.WireId planned.val.WireId :=
  forward.argumentResult.inverseTransportWireEquivHeadOnly
    backward.argumentResult
    forward.sourceRemovedWires_exact forward.localCount_exact
    backward.sourceRemovedWires_exact backward.localCount_exact targetIso

@[simp] theorem inverseTransportWireEquiv_head
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    forward.inverseTransportWireEquiv backward targetIso
        backward.targetWire = forwardWire := by
  unfold inverseTransportWireEquiv
  change forward.wireEquiv.symm
    (targetIso.wires (backward.wireEquiv.symm backward.targetWire)) = _
  calc
    forward.wireEquiv.symm
        (targetIso.wires (backward.wireEquiv.symm backward.targetWire)) =
      forward.wireEquiv.symm (targetIso.wires backwardWire) := by
        congr 2
        rw [← backward.wireEquiv_head]
        exact backward.wireEquiv.left_inv backwardWire
    _ = forward.wireEquiv.symm forward.targetWire :=
      congrArg forward.wireEquiv.symm wireExact
    _ = forwardWire := by
      rw [← forward.wireEquiv_head]
      exact forward.wireEquiv.left_inv forwardWire

/-- The transported region carrier restores the planned root. -/
theorem inverseTransport_root
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val) :
    forward.inverseTransportRegionEquiv backward targetIso
        backward.target.val.root = planned.val.root := by
  unfold inverseTransportRegionEquiv
  change forward.argumentResult.regionEquiv.symm
    (targetIso.regions
      (backward.argumentResult.regionEquiv.symm backward.target.val.root)) = _
  have backwardRoot : backward.target.val.root =
      backward.argumentResult.regionEquiv real.val.root := by
    exact backward.argumentResult.targetRoot_exact.trans
      (backward.argumentResult.regionImage_exact real.val.root)
  rw [backwardRoot]
  have backwardCancel :=
    backward.argumentResult.regionEquiv.left_inv real.val.root
  change backward.argumentResult.regionEquiv.invFun
      (backward.argumentResult.regionEquiv real.val.root) = real.val.root
    at backwardCancel
  calc
    forward.argumentResult.regionEquiv.symm
        (targetIso.regions
          (backward.argumentResult.regionEquiv.symm
            (backward.argumentResult.regionEquiv real.val.root))) =
        forward.argumentResult.regionEquiv.symm
          (targetIso.regions real.val.root) :=
      congrArg (fun value => forward.argumentResult.regionEquiv.symm
        (targetIso.regions value)) backwardCancel
    _ = forward.argumentResult.regionEquiv.symm forward.target.val.root := by
      rw [targetIso.root]
    _ = forward.argumentResult.regionEquiv.symm
        (forward.argumentResult.regionEquiv planned.val.root) := by
      congr 1
      exact forward.argumentResult.targetRoot_exact.trans
        (forward.argumentResult.regionImage_exact planned.val.root)
    _ = planned.val.root := forward.argumentResult.regionEquiv.left_inv _

/-- Region tables commute with the transported inverse carrier. -/
theorem inverseTransport_region_table
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (region : backward.target.val.RegionId) :
    planned.val.regions
        (forward.inverseTransportRegionEquiv backward targetIso region) =
      (backward.target.val.regions region).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
  let realRegion := backward.argumentResult.regionEquiv.symm region
  have backwardData := backward.argumentResult.regionImage_data realRegion
  have backwardRegionExact : backward.argumentResult.regionEquiv realRegion = region :=
    backward.argumentResult.regionEquiv.right_inv region
  rw [backwardRegionExact] at backwardData
  have backwardDataPublic : backward.target.val.regions region =
      (real.val.regions realRegion).rename backward.argumentResult.regionEquiv :=
    backwardData
  have middleData := targetIso.region_table realRegion
  have plannedData := forward.argumentResult.regionImage_data
    (forward.argumentResult.regionEquiv.symm (targetIso.regions realRegion))
  have plannedRegionExact :
      forward.argumentResult.regionEquiv
          (forward.argumentResult.regionEquiv.symm (targetIso.regions realRegion)) =
        targetIso.regions realRegion :=
    forward.argumentResult.regionEquiv.right_inv _
  rw [plannedRegionExact] at plannedData
  unfold inverseTransportRegionEquiv
  change planned.val.regions
      (forward.argumentResult.regionEquiv.symm (targetIso.regions realRegion)) = _
  rw [backwardDataPublic]
  have middleRelation :
      (real.val.regions realRegion).rename targetIso.regions =
        (planned.val.regions
          (forward.argumentResult.regionEquiv.symm
            (targetIso.regions realRegion))).rename
          forward.argumentResult.regionEquiv :=
    middleData.symm.trans plannedData
  cases realData : real.val.regions realRegion with
  | sheet =>
      cases plannedDataExact : planned.val.regions
          (forward.argumentResult.regionEquiv.symm
            (targetIso.regions realRegion)) with
      | sheet => rfl
      | cut parent =>
          rw [realData, plannedDataExact] at middleRelation
          contradiction
  | cut realParent =>
      cases plannedDataExact : planned.val.regions
          (forward.argumentResult.regionEquiv.symm
            (targetIso.regions realRegion)) with
      | sheet =>
          rw [realData, plannedDataExact] at middleRelation
          contradiction
      | cut plannedParent =>
          rw [realData, plannedDataExact] at middleRelation
          simp only [CRegion.rename] at middleRelation
          have parentRelation : targetIso.regions realParent =
              forward.argumentResult.regionEquiv plannedParent :=
            CRegion.cut.inj middleRelation
          congr 1
          unfold ConcreteWirePrimitive.ArgumentResult.inverseTransportRegionEquiv
          change plannedParent = forward.argumentResult.regionEquiv.symm
            (targetIso.regions
              (backward.argumentResult.regionEquiv.symm
                (backward.argumentResult.regionEquiv realParent)))
          have backwardParentCancel :=
            backward.argumentResult.regionEquiv.left_inv realParent
          change backward.argumentResult.regionEquiv.invFun
              (backward.argumentResult.regionEquiv realParent) = realParent
            at backwardParentCancel
          calc
            plannedParent = forward.argumentResult.regionEquiv.symm
                (targetIso.regions realParent) :=
              (forward.argumentResult.regionEquiv.left_inv plannedParent).symm.trans
                (congrArg forward.argumentResult.regionEquiv.symm
                  parentRelation).symm
            _ = forward.argumentResult.regionEquiv.symm
                (targetIso.regions
                  (backward.argumentResult.regionEquiv.symm
                    (backward.argumentResult.regionEquiv realParent))) :=
              congrArg (fun value => forward.argumentResult.regionEquiv.symm
                (targetIso.regions value)) backwardParentCancel.symm



/-- Planned source-site position represented by one real source site after
transport through the supplied target isomorphism. -/
def inverseTransportSitePosition
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.argumentResult.sites.sites.length) :
    Fin forward.argumentResult.sites.sites.length :=
  let sourceEndpoint := (backward.argumentResult.sites.sites.get site).endpoint
  have sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.argumentResult.sites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.argumentResult.sites.sites.get site, List.get_mem _ _, rfl⟩
  let middleEndpoint := targetIso.endpointMap backwardWire sourceEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires forward.targetWire).endpoints := by
    rw [← wireExact]
    exact targetIso.endpointMap_mem backwardWire sourceEndpoint sourceMember
  let middleEndpointPosition := DenseList.index
    (forward.target.val.wires forward.targetWire).endpoints
    middleEndpoint middleMember
  let middlePosition := Fin.cast forward.targetSites.length.symm
    middleEndpointPosition
  let middleNode := (forward.targetSites.sites.get middlePosition).node
  have generated : middleNode ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨forward.targetSites.sites.get middlePosition,
        List.get_mem _ _, rfl⟩
  forward.argumentResult.sourcePositionOfTargetNode forward.targetSites
    middleNode generated

/-- The transported inverse node carrier sends each rebuilt node to the
exact planned source site selected by endpoint transport. -/
theorem inverseTransport_targetNode
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.argumentResult.sites.sites.length) :
    forward.inverseTransportNodeEquiv backward targetIso
        (backward.argumentResult.targetNode site) =
      (forward.argumentResult.sites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node := by
  let backwardNode := (backward.argumentResult.sites.sites.get site).node
  have backwardMember : backwardNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.argumentResult.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.argumentResult.sites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardImage : backward.nodeEquiv backwardNode =
      backward.argumentResult.targetNode site := by
    unfold AppliedArgDrop.nodeEquiv
      ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.argumentResult.nodeImage backwardNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos backwardMember,
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  have backwardInverse : backward.nodeEquiv.symm
      (backward.argumentResult.targetNode site) = backwardNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv backwardNode
  let sourceEndpoint := (backward.argumentResult.sites.sites.get site).endpoint
  have sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.argumentResult.sites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.argumentResult.sites.sites.get site, List.get_mem _ _, rfl⟩
  let middleEndpoint := targetIso.endpointMap backwardWire sourceEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires forward.targetWire).endpoints := by
    rw [← wireExact]
    exact targetIso.endpointMap_mem backwardWire sourceEndpoint sourceMember
  let middleEndpointPosition := DenseList.index
    (forward.target.val.wires forward.targetWire).endpoints
    middleEndpoint middleMember
  let middlePosition := Fin.cast forward.targetSites.length.symm
    middleEndpointPosition
  let middleSite := forward.targetSites.sites.get middlePosition
  have middleNodeExact : middleSite.node = targetIso.nodes backwardNode := by
    have selected := get_of_list_eq forward.targetSites.exhaustive
      middleEndpointPosition
    have endpointExact := DenseList.get_index
      (forward.target.val.wires forward.targetWire).endpoints
      middleEndpoint middleMember
    rw [endpointExact] at selected
    have selectedPosition :
        Fin.cast (congrArg List.length
          forward.targetSites.exhaustive).symm middleEndpointPosition =
          Fin.cast (by simp) middlePosition := by
      apply Fin.ext
      rfl
    rw [selectedPosition] at selected
    have corresponds := targetIso.endpointMap_corresponds backwardWire
      sourceEndpoint sourceMember
    simpa [middleSite, sourceEndpoint, backwardNode, AppliedSite.endpoint]
      using (congrArg CEndpoint.node selected).trans corresponds.1
  have middleGenerated : middleSite.node ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr ⟨middleSite, List.get_mem _ _, rfl⟩
  let plannedPosition := forward.argumentResult.sourcePositionOfTargetNode
    forward.targetSites middleSite.node middleGenerated
  have forwardTarget : forward.argumentResult.targetNode plannedPosition =
      middleSite.node :=
    forward.argumentResult.targetNode_sourcePositionOfTargetNode
      forward.targetSites middleSite.node middleGenerated
  let plannedNode :=
    (forward.argumentResult.sites.sites.get plannedPosition).node
  have plannedMember : plannedNode ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.argumentResult.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨forward.argumentResult.sites.sites.get plannedPosition,
        List.get_mem _ _, rfl⟩
  have forwardImage : forward.nodeEquiv plannedNode =
      forward.argumentResult.targetNode plannedPosition := by
    unfold AppliedArgExtend.nodeEquiv
      ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.argumentResult.nodeImage plannedNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos plannedMember,
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  unfold inverseTransportNodeEquiv
  change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm (backward.argumentResult.targetNode site))) = _
  rw [backwardInverse, ← middleNodeExact,
    ← forwardTarget, ← forwardImage]
  change forward.nodeEquiv.symm (forward.nodeEquiv plannedNode) = plannedNode
  exact forward.nodeEquiv.left_inv plannedNode

/-- The exact forward target node underlying a transported backward site. -/
theorem inverseTransport_middleNode
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.argumentResult.sites.sites.length) :
    targetIso.nodes (backward.argumentResult.sites.sites.get site).node =
      forward.argumentResult.targetNode
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site) := by
  let backwardNode := (backward.argumentResult.sites.sites.get site).node
  have backwardMember : backwardNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.argumentResult.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.argumentResult.sites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardImage : backward.nodeEquiv backwardNode =
      backward.argumentResult.targetNode site := by
    exact backward.nodeEquiv_generated site
  have backwardInverse : backward.nodeEquiv.symm
      (backward.argumentResult.targetNode site) = backwardNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv backwardNode
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedNode :=
    (forward.argumentResult.sites.sites.get plannedPosition).node
  have forwardImage : forward.nodeEquiv plannedNode =
      forward.argumentResult.targetNode plannedPosition := by
    exact forward.nodeEquiv_generated plannedPosition
  have carrierExact := forward.inverseTransport_targetNode backward
    targetIso wireExact site
  unfold inverseTransportNodeEquiv at carrierExact
  change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm (backward.argumentResult.targetNode site))) =
      plannedNode at carrierExact
  rw [backwardInverse] at carrierExact
  have lifted := congrArg forward.nodeEquiv carrierExact
  have forwardCancel := forward.nodeEquiv.right_inv
    (targetIso.nodes backwardNode)
  change forward.nodeEquiv
      (forward.nodeEquiv.symm (targetIso.nodes backwardNode)) =
    targetIso.nodes backwardNode at forwardCancel
  have exactMiddle : targetIso.nodes backwardNode =
      forward.nodeEquiv plannedNode :=
    forwardCancel.symm.trans lifted
  rw [forwardImage] at exactMiddle
  exact exactMiddle



/-- Rebuilt nodes satisfy the transported node-table law; the erased and
reinserted argument vector cancels at the selected position. -/
theorem inverseTransport_generated_node_table
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.argumentResult.sites.sites.length) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso
          (backward.argumentResult.targetNode site)) =
      (backward.target.val.nodes
        (backward.argumentResult.targetNode site)).rename
          (forward.inverseTransportRegionEquiv backward targetIso) := by
  let backwardSite := backward.argumentResult.sites.sites.get site
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedSite := forward.argumentResult.sites.sites.get plannedPosition
  have nodeExact := forward.inverseTransport_targetNode backward
    targetIso wireExact site
  have backwardTargetData : backward.target.val.nodes
      (backward.argumentResult.targetNode site) =
    .atom (backward.argumentResult.regionImage backwardSite.region)
      backward.argumentResult.targetArguments := by
    exact backward.argumentResult.targetNode_data site
  rw [nodeExact, plannedSite.node_data, backwardTargetData]
  have targetNodeExact := forward.inverseTransport_middleNode backward
    targetIso wireExact site
  have mappedData := targetIso.node_table backwardSite.node
  rw [backwardSite.node_data, targetNodeExact] at mappedData
  have forwardTargetData : forward.target.val.nodes
      (forward.argumentResult.targetNode plannedPosition) =
    .atom (forward.argumentResult.regionImage plannedSite.region)
      forward.argumentResult.targetArguments := by
    exact forward.argumentResult.targetNode_data plannedPosition
  rw [forwardTargetData] at mappedData
  have regionExact : forward.argumentResult.regionImage plannedSite.region =
      targetIso.regions backwardSite.region :=
    (CNode.atom.inj mappedData).1
  have restored := forward.inverseTargetArguments_exact backward
    targetIso wireExact
  change backward.argumentResult.targetArguments =
    forward.sourceArgumentList at restored
  rw [restored]
  have plannedArguments : plannedSite.argumentSignatures =
      forward.sourceArgumentList :=
    ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
      forward.sourceArgumentList forward.sourceWire_signature plannedSite
  rw [plannedArguments]
  congr 2
  unfold inverseTransportRegionEquiv
  change plannedSite.region = forward.argumentResult.regionEquiv.symm
    (targetIso.regions
      (backward.argumentResult.regionEquiv.symm
        (backward.argumentResult.regionImage backwardSite.region)))
  rw [backward.argumentResult.regionImage_exact]
  have backwardCancel :=
    backward.argumentResult.regionEquiv.left_inv backwardSite.region
  change backward.argumentResult.regionEquiv.invFun
      (backward.argumentResult.regionEquiv backwardSite.region) =
    backwardSite.region at backwardCancel
  have forwardRegionExact :=
    forward.argumentResult.regionImage_exact plannedSite.region
  calc
    plannedSite.region = forward.argumentResult.regionEquiv.symm
        (forward.argumentResult.regionEquiv plannedSite.region) :=
      (forward.argumentResult.regionEquiv.left_inv plannedSite.region).symm
    _ = forward.argumentResult.regionEquiv.symm
        (forward.argumentResult.regionImage plannedSite.region) := by
      rw [forwardRegionExact]
    _ = forward.argumentResult.regionEquiv.symm
        (targetIso.regions backwardSite.region) :=
      congrArg forward.argumentResult.regionEquiv.symm regionExact
    _ = forward.argumentResult.regionEquiv.symm
        (targetIso.regions
          (backward.argumentResult.regionEquiv.symm
            (backward.argumentResult.regionEquiv backwardSite.region))) :=
      congrArg (fun value => forward.argumentResult.regionEquiv.symm
        (targetIso.regions value)) backwardCancel.symm



/-- A real node retained by extension cannot transport to a generated
forward drop target site. -/
theorem inverseTransport_middleNode_retained
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realNode : real.val.NodeId)
    (retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.argumentResult.sites) :
    targetIso.nodes realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
  intro generated
  unfold ConcreteWirePrimitive.argumentSiteNodes at generated
  rcases List.mem_map.mp generated with
    ⟨middleSite, middleMember, middleNodeExact⟩
  have targetOwner : forward.target.val.endpointOwner?
      ⟨targetIso.nodes realNode, .head⟩ = some forward.targetWire := by
    rw [← middleNodeExact]
    exact middleSite.endpoint_owner
  have mappedData := targetIso.node_table realNode
  have middleData : forward.target.val.nodes (targetIso.nodes realNode) =
      .atom middleSite.region middleSite.argumentSignatures := by
    rw [← middleNodeExact]
    exact middleSite.node_data
  cases sourceData : real.val.nodes realNode with
  | atom region arguments =>
      have sourceOwner := targetIso.atom_owner_backward real.property
        sourceData targetOwner
      have inverseWireExact : targetIso.wires.symm forward.targetWire =
          backwardWire := by
        calc
          targetIso.wires.symm forward.targetWire =
              targetIso.wires.symm (targetIso.wires backwardWire) := by
            rw [wireExact]
          _ = backwardWire := targetIso.wires.left_inv backwardWire
      rw [inverseWireExact] at sourceOwner
      have incident := ConcreteDiagram.endpointOwner?_incident real.val
        ⟨realNode, .head⟩ backwardWire sourceOwner
      rw [← backward.argumentResult.sites.exhaustive] at incident
      rcases List.mem_map.mp incident with
        ⟨sourceSite, sourceMember, endpointExact⟩
      apply retained
      unfold ConcreteWirePrimitive.argumentSiteNodes
      exact List.mem_map.mpr
        ⟨sourceSite, sourceMember,
          congrArg CEndpoint.node endpointExact⟩
  | ref region definition arguments =>
      rw [middleData, sourceData] at mappedData
      contradiction
  | identity region signature arity =>
      rw [middleData, sourceData] at mappedData
      contradiction

/-- Retained extension nodes satisfy the complete transported node-table
law. -/
theorem inverseTransport_retained_node_table
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realNode : real.val.NodeId)
    (retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.argumentResult.sites) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso
          (backward.argumentResult.retainedNodeImage realNode retained)) =
      (backward.target.val.nodes
        (backward.argumentResult.retainedNodeImage realNode retained)).rename
          (forward.inverseTransportRegionEquiv backward targetIso) := by
  have middleRetained := forward.inverseTransport_middleNode_retained
    backward targetIso wireExact realNode retained
  let plannedNode := forward.argumentResult.sourceNodeOfRetainedTarget
    forward.targetSites (targetIso.nodes realNode) middleRetained
  have plannedRetained : plannedNode ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.argumentResult.sites :=
    ConcreteWirePrimitive.sourceRetainedNode_not_removed
      forward.argumentResult.sites
      (forward.argumentResult.retainedBaseNodeOfTarget forward.targetSites
        (targetIso.nodes realNode) middleRetained)
  have backwardImage : backward.nodeEquiv realNode =
      backward.argumentResult.retainedNodeImage realNode retained :=
    backward.nodeEquiv_retained realNode retained
  have backwardInverse : backward.nodeEquiv.symm
      (backward.argumentResult.retainedNodeImage realNode retained) = realNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv realNode
  have forwardInverse : forward.nodeEquiv.symm
      (targetIso.nodes realNode) = plannedNode := by
    unfold AppliedArgExtend.nodeEquiv
      ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.argumentResult.sourceNode forward.targetSites
      (targetIso.nodes realNode) = plannedNode
    unfold ConcreteWirePrimitive.ArgumentResult.sourceNode
    split
    next generated => exact (middleRetained generated).elim
    next _ => rfl
  have carrierExact : forward.inverseTransportNodeEquiv backward targetIso
      (backward.argumentResult.retainedNodeImage realNode retained) =
        plannedNode := by
    unfold inverseTransportNodeEquiv
    change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm
          (backward.argumentResult.retainedNodeImage realNode retained))) = _
    rw [backwardInverse, forwardInverse]
  rw [carrierExact]
  have backwardData : backward.target.val.nodes
      (backward.argumentResult.retainedNodeImage realNode retained) =
        (real.val.nodes realNode).rename backward.argumentResult.regionEquiv :=
    backward.argumentResult.retainedNodeImage_data realNode retained
  rw [backwardData]
  have forwardImage : forward.argumentResult.retainedNodeImage plannedNode
      plannedRetained = targetIso.nodes realNode :=
    forward.argumentResult.retainedNodeImage_sourceNodeOfRetainedTarget
      forward.targetSites (targetIso.nodes realNode) middleRetained
  have forwardData : forward.target.val.nodes (targetIso.nodes realNode) =
      (planned.val.nodes plannedNode).rename forward.argumentResult.regionEquiv := by
    rw [← forwardImage]
    exact forward.argumentResult.retainedNodeImage_data plannedNode plannedRetained
  have middleData := targetIso.node_table realNode
  rw [forwardData] at middleData
  cases realData : real.val.nodes realNode with
  | atom realRegion realArguments =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.atom.inj middleData
          cases parts.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.argumentResult.regionEquiv.left_inv realRegion
          change backward.argumentResult.regionEquiv.invFun
              (backward.argumentResult.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.argumentResult.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.argumentResult.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.argumentResult.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))
      | ref plannedRegion definition plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | identity plannedRegion signature arity =>
          rw [realData, plannedData] at middleData
          contradiction
  | ref realRegion realDefinition realArguments =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | ref plannedRegion plannedDefinition plannedArguments =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.ref.inj middleData
          cases parts.2.1
          cases parts.2.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.argumentResult.regionEquiv.left_inv realRegion
          change backward.argumentResult.regionEquiv.invFun
              (backward.argumentResult.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.argumentResult.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.argumentResult.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.argumentResult.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))
      | identity plannedRegion signature arity =>
          rw [realData, plannedData] at middleData
          contradiction
  | identity realRegion realSignature realArity =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | ref plannedRegion definition plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | identity plannedRegion plannedSignature plannedArity =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.identity.inj middleData
          cases parts.2.1
          cases parts.2.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.argumentResult.regionEquiv.left_inv realRegion
          change backward.argumentResult.regionEquiv.invFun
              (backward.argumentResult.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.argumentResult.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.argumentResult.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.argumentResult.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))

/-- Complete node-table law for the transported inverse drop/extension
carrier. -/
theorem inverseTransport_node_table
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (node : backward.target.val.NodeId) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso node) =
      (backward.target.val.nodes node).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
  let realNode := backward.nodeEquiv.symm node
  have nodeRecover : backward.nodeEquiv realNode = node :=
    backward.nodeEquiv.right_inv node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.argumentResult.sites
  · let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
      backward.argumentResult.sites realNode generated
    have imageExact : backward.nodeEquiv realNode =
        backward.argumentResult.targetNode site := by
      unfold AppliedArgDrop.nodeEquiv
        ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change backward.argumentResult.nodeImage realNode = _
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_pos generated]
    have nodeExact : node = backward.argumentResult.targetNode site :=
      nodeRecover.symm.trans imageExact
    rw [nodeExact]
    exact forward.inverseTransport_generated_node_table backward
      targetIso wireExact site
  · have imageExact : backward.nodeEquiv realNode =
        backward.argumentResult.retainedNodeImage realNode generated :=
      backward.nodeEquiv_retained realNode generated
    have nodeExact : node =
        backward.argumentResult.retainedNodeImage realNode generated :=
      nodeRecover.symm.trans imageExact
    rw [nodeExact]
    exact forward.inverseTransport_retained_node_table backward
      targetIso wireExact realNode generated

/-- The transported inverse wire carrier acts on every inverse-construction
image by composing the three construction-owned wire equivalences. -/
theorem inverseTransport_wireEquiv_image
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (realWire : real.val.WireId) :
    forward.inverseTransportWireEquiv backward targetIso
        (backward.wireEquiv realWire) =
      forward.wireEquiv.symm (targetIso.wires realWire) := by
  unfold inverseTransportWireEquiv
  change forward.wireEquiv.symm
    (targetIso.wires
      (backward.wireEquiv.symm (backward.wireEquiv realWire))) = _
  have backwardCancel := backward.wireEquiv.left_inv realWire
  change backward.wireEquiv.invFun (backward.wireEquiv realWire) =
    realWire at backwardCancel
  exact congrArg (fun value => forward.wireEquiv.symm
    (targetIso.wires value)) backwardCancel



/-- Complete wire-signature law for the transported inverse carrier. -/
theorem inverseTransport_wire_signature
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId) :
    (planned.val.wires
      (forward.inverseTransportWireEquiv backward targetIso targetWire)).sig =
      (backward.target.val.wires targetWire).sig := by
  let realWire := backward.wireEquiv.symm targetWire
  have targetExact : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  rw [← targetExact, forward.inverseTransport_wireEquiv_image]
  by_cases head : realWire = backwardWire
  · rw [head]
    have forwardInverseHead : forward.wireEquiv.symm forward.targetWire =
        forwardWire := by
      rw [← forward.wireEquiv_head]
      exact forward.wireEquiv.left_inv forwardWire
    have backwardTargetSignature :
        (backward.target.val.wires backward.targetWire).sig =
          .rel backward.argumentResult.targetArguments := by
      exact backward.argumentResult.targetWire_signature
    rw [wireExact, forwardInverseHead, backward.wireEquiv_head,
      forward.sourceWire_signature, backwardTargetSignature]
    have restored := forward.inverseTargetArguments_exact backward
      targetIso wireExact
    exact congrArg Sig.rel restored.symm
  · let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
    have plannedImage : forward.wireEquiv plannedWire =
        targetIso.wires realWire :=
      forward.wireEquiv.right_inv (targetIso.wires realWire)
    have plannedDifferent : plannedWire ≠ forwardWire := by
      intro same
      have mapped := congrArg forward.wireEquiv same
      rw [plannedImage, forward.wireEquiv_head] at mapped
      have realExact := targetIso.wires.injective
        (mapped.trans wireExact.symm)
      exact head realExact
    calc
      (planned.val.wires plannedWire).sig =
          (forward.target.val.wires (targetIso.wires realWire)).sig := by
        rw [← plannedImage]
        exact (forward.wireEquiv_retained_signature plannedWire
          plannedDifferent).symm
      _ = (real.val.wires realWire).sig :=
        targetIso.wire_signature realWire
      _ = (backward.target.val.wires
          (backward.wireEquiv realWire)).sig :=
        (backward.wireEquiv_retained_signature realWire head).symm

/-- Complete wire-scope law for the transported inverse carrier. -/
theorem inverseTransport_wire_scope
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId) :
    (planned.val.wires
      (forward.inverseTransportWireEquiv backward targetIso targetWire)).scope =
      forward.inverseTransportRegionEquiv backward targetIso
        (backward.target.val.wires targetWire).scope := by
  let realWire := backward.wireEquiv.symm targetWire
  have targetExact : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  rw [← targetExact, forward.inverseTransport_wireEquiv_image]
  by_cases head : realWire = backwardWire
  · rw [head]
    have forwardInverseHead : forward.wireEquiv.symm forward.targetWire =
        forwardWire := by
      rw [← forward.wireEquiv_head]
      exact forward.wireEquiv.left_inv forwardWire
    rw [wireExact, forwardInverseHead, backward.wireEquiv_head]
    have backwardScope := backward.argumentResult.targetWire_scope_regionImage
    change (backward.target.val.wires backward.targetWire).scope =
        backward.argumentResult.regionImage
          (real.val.wires backwardWire).scope at backwardScope
    have forwardScope := forward.argumentResult.targetWire_scope_regionImage
    change (forward.target.val.wires forward.targetWire).scope =
        forward.argumentResult.regionImage
          (planned.val.wires forwardWire).scope at forwardScope
    have middleScope := targetIso.wire_scope backwardWire
    rw [wireExact] at middleScope
    unfold inverseTransportRegionEquiv
    rw [backwardScope, backward.argumentResult.regionImage_exact]
    have backwardCancel := backward.argumentResult.regionEquiv.left_inv
      (real.val.wires backwardWire).scope
    change backward.argumentResult.regionEquiv.invFun
        (backward.argumentResult.regionEquiv
          (real.val.wires backwardWire).scope) =
      (real.val.wires backwardWire).scope at backwardCancel
    calc
      (planned.val.wires forwardWire).scope =
          forward.argumentResult.regionEquiv.symm
            (forward.argumentResult.regionEquiv
              (planned.val.wires forwardWire).scope) :=
        (forward.argumentResult.regionEquiv.left_inv _).symm
      _ = forward.argumentResult.regionEquiv.symm
          (forward.target.val.wires forward.targetWire).scope := by
        rw [forwardScope, forward.argumentResult.regionImage_exact]
      _ = forward.argumentResult.regionEquiv.symm
          (targetIso.regions (real.val.wires backwardWire).scope) := by
        rw [middleScope]
      _ = forward.argumentResult.regionEquiv.symm
          (targetIso.regions
            (backward.argumentResult.regionEquiv.symm
              (backward.argumentResult.regionEquiv
                (real.val.wires backwardWire).scope))) :=
        congrArg (fun value => forward.argumentResult.regionEquiv.symm
          (targetIso.regions value)) backwardCancel.symm
  · let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
    have plannedImage : forward.wireEquiv plannedWire =
        targetIso.wires realWire :=
      forward.wireEquiv.right_inv (targetIso.wires realWire)
    have plannedDifferent : plannedWire ≠ forwardWire := by
      intro same
      have mapped := congrArg forward.wireEquiv same
      rw [plannedImage, forward.wireEquiv_head] at mapped
      have realExact := targetIso.wires.injective
        (mapped.trans wireExact.symm)
      exact head realExact
    have forwardScope := forward.wireEquiv_retained_scope plannedWire
      plannedDifferent
    rw [plannedImage] at forwardScope
    change (forward.target.val.wires (targetIso.wires realWire)).scope =
      forward.argumentResult.regionEquiv
        (planned.val.wires plannedWire).scope at forwardScope
    have backwardScope := backward.wireEquiv_retained_scope realWire head
    have middleScope := targetIso.wire_scope realWire
    unfold inverseTransportRegionEquiv
    rw [backwardScope]
    have backwardCancel := backward.argumentResult.regionEquiv.left_inv
      (real.val.wires realWire).scope
    change backward.argumentResult.regionEquiv.invFun
        (backward.argumentResult.regionEquiv (real.val.wires realWire).scope) =
      (real.val.wires realWire).scope at backwardCancel
    calc
      (planned.val.wires plannedWire).scope =
          forward.argumentResult.regionEquiv.symm
            (forward.argumentResult.regionEquiv
              (planned.val.wires plannedWire).scope) :=
        (forward.argumentResult.regionEquiv.left_inv _).symm
      _ = forward.argumentResult.regionEquiv.symm
          (forward.target.val.wires (targetIso.wires realWire)).scope := by
        rw [forwardScope]
      _ = forward.argumentResult.regionEquiv.symm
          (targetIso.regions (real.val.wires realWire).scope) := by
        rw [middleScope]
      _ = forward.argumentResult.regionEquiv.symm
          (targetIso.regions
            (backward.argumentResult.regionEquiv.symm
              (backward.argumentResult.regionEquiv
                (real.val.wires realWire).scope))) :=
        congrArg (fun value => forward.argumentResult.regionEquiv.symm
          (targetIso.regions value)) backwardCancel.symm



/-- Pair-specific endpoint transport. Rebuilt application nodes are related
directly in their restored argument coordinate; retained nodes compose the
unchanged construction transports with the supplied suffix isomorphism. -/
def inverseTransportEndpointMap
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount) :
    CEndpoint planned.val.nodeCount :=
  let realNode := backward.nodeEquiv.symm endpoint.node
  if generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites then
    ⟨forward.inverseTransportNodeEquiv backward targetIso endpoint.node,
      endpoint.port⟩
  else
    let realWire := backward.wireEquiv.symm targetWire
    let middleEndpoint := targetIso.endpointMap realWire
      ⟨realNode, endpoint.port⟩
    ⟨forward.nodeEquiv.symm middleEndpoint.node, middleEndpoint.port⟩

/-- Inverse of the pair-specific endpoint transport. -/
def inverseTransportEndpointInverse
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint planned.val.nodeCount) :
    CEndpoint backward.target.val.nodeCount :=
  let middleNode := forward.nodeEquiv endpoint.node
  let realNode := targetIso.nodes.symm middleNode
  if generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites then
    ⟨backward.nodeEquiv realNode, endpoint.port⟩
  else
    let realWire := backward.wireEquiv.symm targetWire
    let middleEndpoint : CEndpoint forward.target.val.nodeCount :=
      ⟨middleNode, endpoint.port⟩
    let realEndpoint := targetIso.endpointInverse realWire middleEndpoint
    ⟨backward.nodeEquiv realEndpoint.node, realEndpoint.port⟩

/-- On retained nodes, the pair transport is exactly suffix composition and
therefore preserves incidence without any argument-coordinate case. -/
theorem inverseTransportEndpointMap_mem_retained
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints)
    (retained : backward.nodeEquiv.symm endpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites) :
    forward.inverseTransportEndpointMap backward targetIso targetWire endpoint
        ∈ (planned.val.wires
          (forward.inverseTransportWireEquiv backward targetIso
            targetWire)).endpoints := by
  let realWire := backward.wireEquiv.symm targetWire
  have backwardWireExact : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  have realMember :
      (⟨backward.nodeEquiv.symm endpoint.node, endpoint.port⟩ :
        CEndpoint real.val.nodeCount) ∈
        (real.val.wires realWire).endpoints := by
    apply backward.retainedEndpointInverse_mem realWire endpoint
    · simpa [backwardWireExact] using member
    · exact retained
  let realEndpoint : CEndpoint real.val.nodeCount :=
    ⟨backward.nodeEquiv.symm endpoint.node, endpoint.port⟩
  let middleEndpoint := targetIso.endpointMap realWire realEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires (targetIso.wires realWire)).endpoints :=
    targetIso.endpointMap_mem realWire realEndpoint realMember
  have middleRetained : middleEndpoint.node ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    have retainedImage := forward.inverseTransport_middleNode_retained
      backward targetIso wireExact
        (backward.nodeEquiv.symm endpoint.node) retained
    have corresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    intro generated
    apply retainedImage
    rw [← corresponds.1]
    exact generated
  let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
  have plannedMember :
      (⟨forward.nodeEquiv.symm middleEndpoint.node, middleEndpoint.port⟩ :
        CEndpoint planned.val.nodeCount) ∈
        (planned.val.wires plannedWire).endpoints := by
    apply forward.retainedEndpointInverse_mem plannedWire middleEndpoint
    · have forwardWireExact : forward.wireEquiv plannedWire =
          targetIso.wires realWire := forward.wireEquiv.right_inv _
      simpa [forwardWireExact] using middleMember
    · intro plannedGenerated
      have generatedImage := forward.nodeEquiv_generated_mem
        (forward.nodeEquiv.symm middleEndpoint.node) plannedGenerated
      apply middleRetained
      exact Eq.mp (congrArg
        (fun node => node ∈
          ConcreteWirePrimitive.argumentSiteNodes forward.targetSites)
        (forward.nodeEquiv.right_inv middleEndpoint.node)) generatedImage
  have endpointExact :
      forward.inverseTransportEndpointMap backward targetIso targetWire
          endpoint =
        (⟨forward.nodeEquiv.symm middleEndpoint.node, middleEndpoint.port⟩ :
          CEndpoint planned.val.nodeCount) := by
    unfold inverseTransportEndpointMap
    rw [dif_neg retained]
  have wireCarrierExact :
      forward.inverseTransportWireEquiv backward targetIso targetWire =
        plannedWire := rfl
  rw [endpointExact, wireCarrierExact]
  exact plannedMember

/-- Rebuilt head endpoints map directly to the original planned heads. -/
theorem inverseTransportEndpointMap_head
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.sourceSites.sites.length) :
    forward.inverseTransportEndpointMap backward targetIso
        backward.targetWire ⟨backward.targetNode site, .head⟩ =
      ⟨(forward.sourceSites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node, .head⟩ ∧
    forward.inverseTransportWireEquiv backward targetIso
        backward.targetWire = forwardWire := by
  let realNode := (backward.sourceSites.sites.get site).node
  have generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.sourceSites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardNode : backward.nodeEquiv realNode =
      backward.targetNode site := backward.nodeEquiv_generated site
  have backwardInverse : backward.nodeEquiv.symm
      (backward.targetNode site) = realNode := by
    rw [← backwardNode]
    exact backward.nodeEquiv.left_inv realNode
  constructor
  · unfold inverseTransportEndpointMap
    rw [show backward.nodeEquiv.symm (backward.targetNode site) = realNode
      from backwardInverse, dif_pos generated]
    congr 1
    exact forward.inverseTransport_targetNode backward targetIso
      wireExact site
  · exact forward.inverseTransportWireEquiv_head backward targetIso
      wireExact

/-- Every rebuilt drop argument endpoint maps at the same restored
coordinate, and its construction-owned wire maps to the exact planned
attachment at that coordinate. -/
theorem inverseTransportEndpointMap_argument
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.sourceSites.sites.length)
    (index : Nat)
    (indexBound : index < backward.targetArgumentList.length) :
    let backwardSite := backward.sourceSites.sites.get site
    let realPosition := restorePosition position index
    let realAttachment :=
      (backwardSite.arguments[realPosition]?).getD backwardWire
    let plannedPosition := forward.inverseTransportSitePosition backward
      targetIso wireExact site
    let plannedSite := forward.sourceSites.sites.get plannedPosition
    let plannedAttachment :=
      (plannedSite.arguments[index]?).getD forwardWire
    forward.inverseTransportEndpointMap backward targetIso
        (backward.wireEquiv realAttachment)
        ⟨backward.targetNode site, .arg index⟩ =
      ⟨plannedSite.node, .arg index⟩ ∧
    forward.inverseTransportWireEquiv backward targetIso
        (backward.wireEquiv realAttachment) = plannedAttachment ∧
    backward.target.val.endpointOwner?
        ⟨backward.targetNode site, .arg index⟩ =
      some (backward.wireEquiv realAttachment) := by
  dsimp only
  let backwardSite := backward.sourceSites.sites.get site
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedSite := forward.sourceSites.sites.get plannedPosition
  have sourceArguments := forward.inverseSourceArguments_exact backward
    targetIso wireExact
  have plannedSiteLength : plannedSite.arguments.length =
      forward.sourceArgumentList.length :=
    plannedSite.arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          forward.sourceArgumentList forward.sourceWire_signature plannedSite))
  have restored := forward.inverseTargetArguments_exact backward
    targetIso wireExact
  have plannedArgumentBound : index < plannedSite.arguments.length := by
    rw [plannedSiteLength, ← restored]
    exact indexBound
  have plannedAttachmentGet : plannedSite.arguments[index]? =
      some ((plannedSite.arguments[index]?).getD forwardWire) := by
    rw [List.getElem?_eq_getElem plannedArgumentBound]
    simp
  have insertedGet := insertAt_getElem?_restorePosition plannedSite.arguments
    position index ((attachments[plannedPosition.val]?).getD forwardWire)
    (by rw [plannedSiteLength]; exact forward.positionValid)
    plannedArgumentBound
  rw [plannedAttachmentGet] at insertedGet
  have forwardTargetBound : restorePosition position index <
      forward.targetArgumentList.length := by
    rw [AppliedArgExtend.targetArgumentList,
      forward.targetArguments_exact,
      insertAt_length_of_le forward.sourceArgumentList position newArgument
        forward.positionValid, ← plannedSiteLength]
    unfold restorePosition
    split <;> omega
  have forwardOwner := forward.generatedArgument_endpointOwner_of_selected
    plannedPosition (restorePosition position index) forwardTargetBound
      ((plannedSite.arguments[index]?).getD forwardWire) insertedGet
  have backwardSiteLength : backwardSite.arguments.length =
      backward.sourceArgumentList.length :=
    backwardSite.arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          backward.sourceArgumentList backward.sourceWire_signature
          backwardSite))
  have sourceLength : backward.sourceArgumentList.length =
      forward.sourceArgumentList.length + 1 := by
    rw [sourceArguments, AppliedArgExtend.targetArgumentList,
      forward.targetArguments_exact,
      insertAt_length_of_le forward.sourceArgumentList position newArgument
        forward.positionValid]
  have realPositionBound : restorePosition position index <
      backwardSite.arguments.length := by
    rw [backwardSiteLength, sourceLength]
    unfold restorePosition
    split <;> omega
  let realAttachment :=
    (backwardSite.arguments[restorePosition position index]?).getD backwardWire
  have realAttachmentGet :
      backwardSite.arguments[restorePosition position index]? =
        some realAttachment := by
    unfold realAttachment
    rw [List.getElem?_eq_getElem realPositionBound]
    simp
  have erasedGet :
      (ConcreteWirePrimitive.eraseAt backwardSite.arguments position)[index]? =
        some realAttachment := by
    rw [← eraseAt_getElem?_restorePosition backwardSite.arguments position
      index]
    · exact realAttachmentGet
    · rw [backwardSiteLength, sourceLength]
      have positionValid := forward.positionValid
      omega
    · rw [backwardSiteLength, sourceLength]
      rw [plannedSiteLength] at plannedArgumentBound
      omega
  have backwardOwner := backward.generatedArgument_endpointOwner_of_selected
    site index indexBound realAttachment erasedGet
  have backwardNodeData := backwardSite.node_data
  have middleOwner := targetIso.atom_owner_forward real.property
    forward.target.property backwardNodeData
      (backwardSite.argument_owner (restorePosition position index)
        realPositionBound)
  have realAttachmentExact :
      backwardSite.arguments[restorePosition position index]'
        realPositionBound = realAttachment := by
    simp [realAttachment, List.getElem?_eq_getElem, realPositionBound]
  rw [realAttachmentExact] at middleOwner
  have middleNode := forward.inverseTransport_middleNode backward targetIso
    wireExact site
  change targetIso.nodes backwardSite.node =
    forward.targetNode plannedPosition at middleNode
  rw [middleNode] at middleOwner
  have middleWire : targetIso.wires realAttachment =
      forward.wireEquiv
        ((plannedSite.arguments[index]?).getD forwardWire) :=
    Option.some.inj (middleOwner.symm.trans forwardOwner)
  have generated : backwardSite.node ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr ⟨backwardSite, List.get_mem _ _, rfl⟩
  have backwardNode : backward.nodeEquiv backwardSite.node =
      backward.targetNode site := backward.nodeEquiv_generated site
  have backwardInverse : backward.nodeEquiv.symm
      (backward.targetNode site) = backwardSite.node := by
    rw [← backwardNode]
    exact backward.nodeEquiv.left_inv backwardSite.node
  constructor
  · unfold inverseTransportEndpointMap
    rw [backwardInverse, dif_pos generated]
    congr 1
    exact forward.inverseTransport_targetNode backward targetIso wireExact site
  · constructor
    · rw [forward.inverseTransport_wireEquiv_image backward targetIso
        realAttachment, middleWire]
      exact forward.wireEquiv.left_inv
        ((plannedSite.arguments[index]?).getD forwardWire)
    · exact backwardOwner

private theorem dropGeneratedHead_endpointOwner
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (site : Fin applied.sourceSites.sites.length) :
    applied.target.val.endpointOwner?
        ⟨applied.targetNode site, .head⟩ = some applied.targetWire := by
  have generatedTarget :=
    applied.argumentResult.generatedNode_targetSiteNode applied.targetSites site
  unfold ConcreteWirePrimitive.argumentSiteNodes at generatedTarget
  rcases List.mem_map.mp generatedTarget with
    ⟨targetSite, _targetMember, targetNodeExact⟩
  have owner := targetSite.endpoint_owner
  change applied.target.val.endpointOwner?
      ⟨targetSite.node, .head⟩ = some applied.targetWire at owner
  rw [targetNodeExact] at owner
  exact owner

private theorem dropGeneratedArgument_bound
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (site : Fin applied.sourceSites.sites.length)
    (index : Nat)
    (required : .arg index ∈
      applied.target.val.requiredPorts (applied.targetNode site)) :
    index < applied.targetArgumentList.length := by
  change .arg index ∈ applied.argumentResult.checked.val.requiredPorts
    (applied.argumentResult.targetNode site) at required
  rw [ConcreteDiagram.requiredPorts,
    applied.argumentResult.targetNode_data site] at required
  simpa [AppliedArgDrop.targetArgumentList] using required

private theorem dropGeneratedIdentity_not_required
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (site : Fin applied.sourceSites.sites.length)
    (index : Nat) :
    .identity index ∉
      applied.target.val.requiredPorts (applied.targetNode site) := by
  change .identity index ∉
    applied.argumentResult.checked.val.requiredPorts
      (applied.argumentResult.targetNode site)
  rw [ConcreteDiagram.requiredPorts,
    applied.argumentResult.targetNode_data site]
  simp

/-- The pair-specific endpoint map preserves incidence on every inverse-drop
target wire. -/
theorem inverseTransportEndpointMap_mem
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    forward.inverseTransportEndpointMap backward targetIso targetWire endpoint
        ∈ (planned.val.wires
          (forward.inverseTransportWireEquiv backward targetIso
            targetWire)).endpoints := by
  rcases endpoint with ⟨targetNode, port⟩
  let realNode := backward.nodeEquiv.symm targetNode
  by_cases retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · exact forward.inverseTransportEndpointMap_mem_retained backward targetIso
      wireExact targetWire ⟨targetNode, port⟩ member retained
  · have generated : realNode ∈
        ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites :=
      Classical.not_not.mp retained
    let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
      backward.sourceSites realNode generated
    let backwardSite := backward.sourceSites.sites.get site
    have siteNode : backwardSite.node = realNode :=
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
        backward.sourceSites realNode generated
    have nodeImage : backward.nodeEquiv realNode =
        backward.targetNode site := by
      rw [← siteNode]
      exact backward.nodeEquiv_generated site
    have nodeRecover : backward.nodeEquiv realNode = targetNode :=
      backward.nodeEquiv.right_inv targetNode
    have targetNodeExact : targetNode = backward.targetNode site :=
      nodeRecover.symm.trans nodeImage
    rw [targetNodeExact] at member ⊢
    have required : port ∈ backward.target.val.requiredPorts
        (backward.targetNode site) :=
      ConcreteDiagram.incident_port_required definitions backward.target.val
        backward.target.property targetWire
          ⟨backward.targetNode site, port⟩ member
    have actualOwner : backward.target.val.endpointOwner?
        ⟨backward.targetNode site, port⟩ = some targetWire :=
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions
        backward.target.val backward.target.property
          (backward.targetNode site) port required targetWire member
    let plannedPosition := forward.inverseTransportSitePosition backward
      targetIso wireExact site
    let plannedSite := forward.sourceSites.sites.get plannedPosition
    cases port with
    | head =>
        have generatedOwner := dropGeneratedHead_endpointOwner backward site
        have targetWireExact : targetWire = backward.targetWire :=
          Option.some.inj (actualOwner.symm.trans generatedOwner)
        subst targetWire
        have transported := forward.inverseTransportEndpointMap_head backward
          targetIso wireExact site
        rw [transported.1, transported.2]
        exact ConcreteDiagram.endpointOwner?_incident planned.val
          ⟨plannedSite.node, .head⟩ forwardWire plannedSite.endpoint_owner
    | arg index =>
        have indexBound := dropGeneratedArgument_bound backward site index
          required
        have transported := forward.inverseTransportEndpointMap_argument
          backward targetIso wireExact site index indexBound
        let realAttachment :=
          (backwardSite.arguments[restorePosition position index]?).getD
            backwardWire
        let plannedAttachment :=
          (plannedSite.arguments[index]?).getD forwardWire
        have targetWireExact : targetWire =
            backward.wireEquiv realAttachment :=
          Option.some.inj (actualOwner.symm.trans transported.2.2)
        subst targetWire
        rw [transported.1, transported.2.1]
        have restored := forward.inverseTargetArguments_exact backward
          targetIso wireExact
        have plannedSiteLength : plannedSite.arguments.length =
            forward.sourceArgumentList.length :=
          plannedSite.arguments_length.trans
            (congrArg List.length
              (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
                forward.sourceArgumentList forward.sourceWire_signature
                plannedSite))
        have plannedBound : index < plannedSite.arguments.length := by
          rw [plannedSiteLength, ← restored]
          exact indexBound
        have owner := plannedSite.argument_owner index plannedBound
        have attachmentExact :
            plannedSite.arguments[index]'plannedBound =
              plannedAttachment := by
          simp [plannedAttachment, plannedBound]
        rw [attachmentExact] at owner
        exact ConcreteDiagram.endpointOwner?_incident planned.val
          ⟨plannedSite.node, .arg index⟩ plannedAttachment owner
    | identity index =>
        exact (dropGeneratedIdentity_not_required backward site index
          required).elim



theorem inverseTransportEndpointInverse_mem
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId)
    (candidate : CEndpoint planned.val.nodeCount)
    (member : candidate ∈
      (planned.val.wires
        (forward.inverseTransportWireEquiv backward targetIso
          targetWire)).endpoints) :
    forward.inverseTransportEndpointInverse backward targetIso targetWire
        candidate ∈
      (backward.target.val.wires targetWire).endpoints := by
  rcases candidate with ⟨plannedNode, port⟩
  let middleNode := forward.nodeEquiv plannedNode
  let realNode := targetIso.nodes.symm middleNode
  let realWire := backward.wireEquiv.symm targetWire
  let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
  have carrierWire :
      forward.inverseTransportWireEquiv backward targetIso targetWire =
        plannedWire := rfl
  rw [carrierWire] at member
  have backwardWireRecover : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  have forwardWireRecover : forward.wireEquiv plannedWire =
      targetIso.wires realWire := forward.wireEquiv.right_inv _
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
      backward.sourceSites realNode generated
    let backwardSite := backward.sourceSites.sites.get site
    have siteNode : backwardSite.node = realNode :=
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_exact
        backward.sourceSites realNode generated
    let plannedPosition := forward.inverseTransportSitePosition backward
      targetIso wireExact site
    let plannedSite := forward.sourceSites.sites.get plannedPosition
    have middleNodeRecover : targetIso.nodes realNode = middleNode := by
      unfold realNode
      exact targetIso.nodes.right_inv middleNode
    have mappedMiddle := forward.inverseTransport_middleNode backward
      targetIso wireExact site
    change targetIso.nodes backwardSite.node =
      forward.targetNode plannedPosition at mappedMiddle
    rw [siteNode, middleNodeRecover] at mappedMiddle
    have plannedImage : forward.nodeEquiv plannedSite.node =
        forward.targetNode plannedPosition :=
      forward.nodeEquiv_generated plannedPosition
    have plannedNodeExact : plannedNode = plannedSite.node := by
      apply forward.nodeEquiv.injective
      exact mappedMiddle.trans plannedImage.symm
    rw [plannedNodeExact] at member ⊢
    have required : port ∈ planned.val.requiredPorts plannedSite.node :=
      ConcreteDiagram.incident_port_required definitions planned.val
        planned.property plannedWire ⟨plannedSite.node, port⟩ member
    have actualOwner : planned.val.endpointOwner?
        ⟨plannedSite.node, port⟩ = some plannedWire :=
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions planned.val
        planned.property plannedSite.node port required plannedWire member
    have inverseEndpointExact :
        forward.inverseTransportEndpointInverse backward targetIso targetWire
          ⟨plannedSite.node, port⟩ =
        ⟨backward.targetNode site, port⟩ := by
      unfold inverseTransportEndpointInverse
      have inverseRealExact : targetIso.nodes.symm
          (forward.nodeEquiv plannedSite.node) = realNode := by
        rw [← plannedNodeExact]
      dsimp only
      rw [inverseRealExact]
      rw [dif_pos generated, ← siteNode]
      congr 1
      exact backward.nodeEquiv_generated site
    rw [inverseEndpointExact]
    cases port with
    | head =>
        have plannedOwner := plannedSite.endpoint_owner
        have plannedWireHead : plannedWire = forwardWire :=
          Option.some.inj (actualOwner.symm.trans plannedOwner)
        have transported := forward.inverseTransportEndpointMap_head backward
          targetIso wireExact site
        have targetWireExact : targetWire = backward.targetWire := by
          apply (forward.inverseTransportWireEquiv backward targetIso).injective
          rw [transported.2, carrierWire, plannedWireHead]
        rw [targetWireExact]
        exact ConcreteDiagram.endpointOwner?_incident backward.target.val
          ⟨backward.targetNode site, .head⟩ backward.targetWire
            (dropGeneratedHead_endpointOwner backward site)
    | arg index =>
        have plannedBound : index < plannedSite.arguments.length := by
          have signatureBound : index <
              plannedSite.argumentSignatures.length := by
            simpa [ConcreteDiagram.requiredPorts, plannedSite.node_data]
              using required
          simpa [plannedSite.arguments_length] using signatureBound
        have plannedAttachmentExact :
            plannedSite.arguments[index]'plannedBound =
              (plannedSite.arguments[index]?).getD forwardWire := by
          simp [plannedBound]
        have plannedOwner := plannedSite.argument_owner index plannedBound
        rw [plannedAttachmentExact] at plannedOwner
        have plannedWireArgument : plannedWire =
            (plannedSite.arguments[index]?).getD forwardWire :=
          Option.some.inj (actualOwner.symm.trans plannedOwner)
        have restored := forward.inverseTargetArguments_exact backward
          targetIso wireExact
        have plannedSiteLength : plannedSite.arguments.length =
            forward.sourceArgumentList.length := by
          exact plannedSite.arguments_length.trans
            (congrArg List.length
              (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
                forward.sourceArgumentList forward.sourceWire_signature
                plannedSite))
        have indexBound : index < backward.targetArgumentList.length := by
          rw [restored, ← plannedSiteLength]
          exact plannedBound
        have transported := forward.inverseTransportEndpointMap_argument
          backward targetIso wireExact site index indexBound
        let realAttachment :=
          (backwardSite.arguments[restorePosition position index]?).getD
            backwardWire
        have targetWireExact : targetWire =
            backward.wireEquiv realAttachment := by
          apply (forward.inverseTransportWireEquiv backward targetIso).injective
          rw [transported.2.1, carrierWire, plannedWireArgument]
        rw [targetWireExact]
        exact ConcreteDiagram.endpointOwner?_incident backward.target.val
          ⟨backward.targetNode site, .arg index⟩
            (backward.wireEquiv realAttachment) transported.2.2
    | identity index =>
        simp [ConcreteDiagram.requiredPorts, plannedSite.node_data] at required
  · have middleRetained := forward.inverseTransport_middleNode_retained
      backward targetIso wireExact realNode generated
    have plannedRetained : plannedNode ∉
        ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
      intro plannedGenerated
      apply middleRetained
      have imageGenerated := forward.nodeEquiv_generated_mem plannedNode
        plannedGenerated
      have realRecover : targetIso.nodes realNode = middleNode := by
        unfold realNode
        exact targetIso.nodes.right_inv middleNode
      rw [realRecover]
      exact imageGenerated
    let middleEndpoint : CEndpoint forward.target.val.nodeCount :=
      ⟨middleNode, port⟩
    have middleMember : middleEndpoint ∈
        (forward.target.val.wires (targetIso.wires realWire)).endpoints := by
      have pushed := forward.retainedEndpointImage_mem plannedWire
        ⟨plannedNode, port⟩ member plannedRetained
      rw [forwardWireRecover] at pushed
      exact pushed
    let realEndpoint := targetIso.endpointInverse realWire middleEndpoint
    have realMember : realEndpoint ∈
        (real.val.wires realWire).endpoints :=
      targetIso.endpointInverse_mem realWire middleEndpoint middleMember
    have corresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    rw [targetIso.endpointMap_right_inv realWire middleEndpoint middleMember]
      at corresponds
    have realEndpointNode : realEndpoint.node = realNode := by
      apply targetIso.nodes.injective
      have realRecover : targetIso.nodes realNode = middleNode := by
        unfold realNode
        exact targetIso.nodes.right_inv middleNode
      exact corresponds.1.symm.trans realRecover.symm
    have finalMember := backward.retainedEndpointImage_mem realWire
      realEndpoint realMember (by simpa [realEndpointNode] using generated)
    rw [backwardWireRecover] at finalMember
    have generatedRaw : targetIso.nodes.symm
        (forward.nodeEquiv plannedNode) ∉
          ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
      simpa [realNode, middleNode] using generated
    unfold inverseTransportEndpointInverse
    dsimp only
    rw [dif_neg generatedRaw]
    exact finalMember

/-- The pair endpoint inverse cancels the map on incident inverse-extension
endpoints. -/
theorem inverseTransportEndpointInverse_map
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    forward.inverseTransportEndpointInverse backward targetIso targetWire
        (forward.inverseTransportEndpointMap backward targetIso targetWire
          endpoint) = endpoint := by
  let realNode := backward.nodeEquiv.symm endpoint.node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · have backwardRecover : backward.nodeEquiv realNode = endpoint.node :=
      backward.nodeEquiv.right_inv endpoint.node
    unfold inverseTransportEndpointMap
    rw [show backward.nodeEquiv.symm endpoint.node = realNode from rfl,
      dif_pos generated]
    unfold inverseTransportEndpointInverse
    dsimp only
    have forwardRecover : forward.nodeEquiv
        (forward.inverseTransportNodeEquiv backward targetIso endpoint.node) =
      targetIso.nodes realNode := by
      unfold inverseTransportNodeEquiv
        ConcreteWirePrimitive.ArgumentResult.inverseTransportNodeEquiv
      change forward.nodeEquiv
          (forward.nodeEquiv.symm
            (targetIso.nodes (backward.nodeEquiv.symm endpoint.node))) = _
      rw [show backward.nodeEquiv.symm endpoint.node = realNode from rfl]
      exact forward.nodeEquiv.right_inv _
    rw [forwardRecover]
    have isoRecover := targetIso.nodes.left_inv realNode
    change targetIso.nodes.symm (targetIso.nodes realNode) = realNode
      at isoRecover
    rw [isoRecover, dif_pos generated, backwardRecover]
  · let realWire := backward.wireEquiv.symm targetWire
    have backwardWireRecover : backward.wireEquiv realWire = targetWire :=
      backward.wireEquiv.right_inv targetWire
    have realMember :
        (⟨realNode, endpoint.port⟩ : CEndpoint real.val.nodeCount) ∈
          (real.val.wires realWire).endpoints := by
      apply backward.retainedEndpointInverse_mem realWire endpoint
      · simpa [backwardWireRecover] using member
      · exact generated
    let realEndpoint : CEndpoint real.val.nodeCount :=
      ⟨realNode, endpoint.port⟩
    let middleEndpoint := targetIso.endpointMap realWire realEndpoint
    have middleMember : middleEndpoint ∈
        (forward.target.val.wires (targetIso.wires realWire)).endpoints :=
      targetIso.endpointMap_mem realWire realEndpoint realMember
    have middleCorresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    have inverseReal : targetIso.nodes.symm middleEndpoint.node = realNode := by
      calc
        targetIso.nodes.symm middleEndpoint.node =
            targetIso.nodes.symm (targetIso.nodes realNode) :=
          congrArg targetIso.nodes.symm middleCorresponds.1
        _ = realNode := targetIso.nodes.left_inv realNode
    unfold inverseTransportEndpointMap
    rw [show backward.nodeEquiv.symm endpoint.node = realNode from rfl,
      dif_neg generated]
    unfold inverseTransportEndpointInverse
    dsimp only
    have forwardCancel := forward.nodeEquiv.right_inv middleEndpoint.node
    change forward.nodeEquiv (forward.nodeEquiv.symm middleEndpoint.node) =
      middleEndpoint.node at forwardCancel
    rw [forwardCancel, inverseReal, dif_neg generated]
    have targetCancel := targetIso.endpointMap_left_inv realWire realEndpoint
      realMember
    rw [targetCancel]
    simp [realEndpoint, realNode, backward.nodeEquiv.right_inv]

/-- The pair endpoint map cancels its inverse on incident planned
endpoints. -/
theorem inverseTransportEndpointMap_inverse
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetWire : backward.target.val.WireId)
    (candidate : CEndpoint planned.val.nodeCount)
    (member : candidate ∈
      (planned.val.wires
        (forward.inverseTransportWireEquiv backward targetIso
          targetWire)).endpoints) :
    forward.inverseTransportEndpointMap backward targetIso targetWire
        (forward.inverseTransportEndpointInverse backward targetIso targetWire
          candidate) = candidate := by
  let middleNode := forward.nodeEquiv candidate.node
  let realNode := targetIso.nodes.symm middleNode
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · unfold inverseTransportEndpointInverse
    dsimp only
    rw [show targetIso.nodes.symm (forward.nodeEquiv candidate.node) = realNode
      from rfl, dif_pos generated]
    unfold inverseTransportEndpointMap
    dsimp only
    have backwardCancel := backward.nodeEquiv.left_inv realNode
    change backward.nodeEquiv.symm (backward.nodeEquiv realNode) = realNode
      at backwardCancel
    rw [backwardCancel, dif_pos generated]
    congr 1
    unfold inverseTransportNodeEquiv
      ConcreteWirePrimitive.ArgumentResult.inverseTransportNodeEquiv
    change forward.nodeEquiv.symm
        (targetIso.nodes
          (backward.nodeEquiv.symm (backward.nodeEquiv realNode))) =
      candidate.node
    rw [backwardCancel]
    have targetCancel := targetIso.nodes.right_inv middleNode
    change targetIso.nodes (targetIso.nodes.symm middleNode) = middleNode
      at targetCancel
    rw [show realNode = targetIso.nodes.symm middleNode from rfl,
      targetCancel]
    exact forward.nodeEquiv.left_inv candidate.node
  · let realWire := backward.wireEquiv.symm targetWire
    let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
    have carrierWire :
        forward.inverseTransportWireEquiv backward targetIso targetWire =
          plannedWire := rfl
    have plannedMember : candidate ∈
        (planned.val.wires plannedWire).endpoints := by
      simpa [carrierWire] using member
    have realRecover : targetIso.nodes realNode = middleNode := by
      unfold realNode
      exact targetIso.nodes.right_inv middleNode
    have middleRetained := forward.inverseTransport_middleNode_retained
      backward targetIso wireExact realNode generated
    have plannedRetained : candidate.node ∉
        ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites := by
      intro plannedGenerated
      apply middleRetained
      rw [realRecover]
      exact forward.nodeEquiv_generated_mem candidate.node plannedGenerated
    let middleEndpoint : CEndpoint forward.target.val.nodeCount :=
      ⟨middleNode, candidate.port⟩
    have forwardWireRecover : forward.wireEquiv plannedWire =
        targetIso.wires realWire := forward.wireEquiv.right_inv _
    have middleMember : middleEndpoint ∈
        (forward.target.val.wires (targetIso.wires realWire)).endpoints := by
      have pushed := forward.retainedEndpointImage_mem plannedWire candidate
        plannedMember plannedRetained
      rw [forwardWireRecover] at pushed
      exact pushed
    let realEndpoint := targetIso.endpointInverse realWire middleEndpoint
    have realMember : realEndpoint ∈
        (real.val.wires realWire).endpoints :=
      targetIso.endpointInverse_mem realWire middleEndpoint middleMember
    have corresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    rw [targetIso.endpointMap_right_inv realWire middleEndpoint middleMember]
      at corresponds
    have realEndpointNode : realEndpoint.node = realNode := by
      apply targetIso.nodes.injective
      exact corresponds.1.symm.trans realRecover.symm
    have generatedEndpoint : realEndpoint.node ∉
        ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites := by
      simpa [realEndpointNode] using generated
    unfold inverseTransportEndpointInverse
    dsimp only
    rw [show targetIso.nodes.symm (forward.nodeEquiv candidate.node) = realNode
      from rfl, dif_neg generated]
    unfold inverseTransportEndpointMap
    dsimp only
    have backwardCancel := backward.nodeEquiv.left_inv realEndpoint.node
    change backward.nodeEquiv.symm (backward.nodeEquiv realEndpoint.node) =
      realEndpoint.node at backwardCancel
    rw [backwardCancel, dif_neg generatedEndpoint]
    have targetCancel := targetIso.endpointMap_right_inv realWire
      middleEndpoint middleMember
    rw [targetCancel]
    simp [middleEndpoint, middleNode, forward.nodeEquiv.left_inv]

/-- The endpoint map uses exactly the transported node carrier. -/
theorem inverseTransportEndpointMap_node
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    (forward.inverseTransportEndpointMap backward targetIso targetWire
      endpoint).node =
      forward.inverseTransportNodeEquiv backward targetIso endpoint.node := by
  let realNode := backward.nodeEquiv.symm endpoint.node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · unfold inverseTransportEndpointMap
    rw [show backward.nodeEquiv.symm endpoint.node = realNode from rfl,
      dif_pos generated]
  · let realWire := backward.wireEquiv.symm targetWire
    have backwardWireRecover : backward.wireEquiv realWire = targetWire :=
      backward.wireEquiv.right_inv targetWire
    have realMember :
        (⟨realNode, endpoint.port⟩ : CEndpoint real.val.nodeCount) ∈
          (real.val.wires realWire).endpoints := by
      apply backward.retainedEndpointInverse_mem realWire endpoint
      · simpa [backwardWireRecover] using member
      · exact generated
    let realEndpoint : CEndpoint real.val.nodeCount :=
      ⟨realNode, endpoint.port⟩
    let middleEndpoint := targetIso.endpointMap realWire realEndpoint
    have corresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    unfold inverseTransportEndpointMap
    rw [show backward.nodeEquiv.symm endpoint.node = realNode from rfl,
      dif_neg generated]
    unfold inverseTransportNodeEquiv
      ConcreteWirePrimitive.ArgumentResult.inverseTransportNodeEquiv
    change forward.nodeEquiv.symm middleEndpoint.node =
      forward.nodeEquiv.symm (targetIso.nodes realNode)
    exact congrArg forward.nodeEquiv.symm corresponds.1

/-- The endpoint map preserves every non-identity port exactly and can only
change storage indices between corresponding identity ports. -/
theorem inverseTransportEndpointMap_port_shape
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    (forward.inverseTransportEndpointMap backward targetIso
        targetWire endpoint).port = endpoint.port ∨
      ∃ sourceIndex targetIndex,
        endpoint.port = .identity sourceIndex ∧
          (forward.inverseTransportEndpointMap backward targetIso
            targetWire endpoint).port = .identity targetIndex := by
  let realNode := backward.nodeEquiv.symm endpoint.node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.sourceSites
  · left
    unfold inverseTransportEndpointMap
    rw [show backward.nodeEquiv.symm endpoint.node = realNode from rfl,
      dif_pos generated]
  · let realWire := backward.wireEquiv.symm targetWire
    have backwardWireRecover : backward.wireEquiv realWire = targetWire :=
      backward.wireEquiv.right_inv targetWire
    let realEndpoint : CEndpoint real.val.nodeCount :=
      ⟨realNode, endpoint.port⟩
    have realMember : realEndpoint ∈
        (real.val.wires realWire).endpoints := by
      apply backward.retainedEndpointInverse_mem realWire endpoint
      · simpa [backwardWireRecover] using member
      · exact generated
    let middleEndpoint := targetIso.endpointMap realWire realEndpoint
    have middleMember := targetIso.endpointMap_mem realWire realEndpoint
      realMember
    have corresponds := targetIso.endpointMap_corresponds realWire
      realEndpoint realMember
    have mappedPort :
        (forward.inverseTransportEndpointMap backward targetIso
          targetWire endpoint).port = middleEndpoint.port := by
      unfold inverseTransportEndpointMap
      rw [show backward.nodeEquiv.symm endpoint.node = realNode from rfl,
        dif_neg generated]
    unfold PortCorresponds at corresponds
    cases realData : real.val.nodes realEndpoint.node with
    | atom region arguments =>
        rw [realData] at corresponds
        cases middleData : forward.target.val.nodes middleEndpoint.node <;>
          simp [middleData] at corresponds
        all_goals exact Or.inl (mappedPort.trans corresponds.2)
    | ref region definition arguments =>
        rw [realData] at corresponds
        cases middleData : forward.target.val.nodes middleEndpoint.node <;>
          simp [middleData] at corresponds
        all_goals exact Or.inl (mappedPort.trans corresponds.2)
    | identity region signature arity =>
        rw [realData] at corresponds
        cases middleData : forward.target.val.nodes middleEndpoint.node with
        | atom targetRegion targetArguments =>
            change forward.target.val.nodes
                (targetIso.endpointMap realWire realEndpoint).node =
              .atom targetRegion targetArguments at middleData
            simp [middleData] at corresponds
            exact Or.inl (mappedPort.trans corresponds.2)
        | ref targetRegion definition targetArguments =>
            change forward.target.val.nodes
                (targetIso.endpointMap realWire realEndpoint).node =
              .ref targetRegion definition targetArguments at middleData
            simp [middleData] at corresponds
            exact Or.inl (mappedPort.trans corresponds.2)
        | identity targetRegion targetSignature targetArity =>
            change forward.target.val.nodes
                (targetIso.endpointMap realWire realEndpoint).node =
              .identity targetRegion targetSignature targetArity at middleData
            have sourceRequired := ConcreteDiagram.incident_port_required
              definitions real.val real.property realWire realEndpoint
                realMember
            rw [ConcreteDiagram.requiredPorts, realData] at sourceRequired
            rcases List.mem_map.mp sourceRequired with
              ⟨sourceIndex, _sourceBound, sourcePort⟩
            have middleRequired := ConcreteDiagram.incident_port_required
              definitions forward.target.val forward.target.property
                (targetIso.wires realWire) middleEndpoint middleMember
            rw [ConcreteDiagram.requiredPorts, middleData] at middleRequired
            rcases List.mem_map.mp middleRequired with
              ⟨targetIndex, _targetBound, targetPort⟩
            exact Or.inr ⟨sourceIndex, targetIndex, sourcePort.symm,
              mappedPort.trans targetPort.symm⟩

/-- The endpoint map satisfies the exact concrete port correspondence for
the transported node carrier. -/
theorem inverseTransportEndpointMap_corresponds
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint backward.target.val.nodeCount)
    (member : endpoint ∈
      (backward.target.val.wires targetWire).endpoints) :
    PortCorresponds backward.target.val planned.val
      (forward.inverseTransportNodeEquiv backward targetIso) endpoint
      (forward.inverseTransportEndpointMap backward targetIso
        targetWire endpoint) := by
  let mapped := forward.inverseTransportEndpointMap backward targetIso
    targetWire endpoint
  have mappedNode : mapped.node =
      forward.inverseTransportNodeEquiv backward targetIso endpoint.node :=
    forward.inverseTransportEndpointMap_node targetIso wireExact backward
      targetWire endpoint member
  have mappedData : planned.val.nodes mapped.node =
      (backward.target.val.nodes endpoint.node).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
    rw [mappedNode]
    exact forward.inverseTransport_node_table backward targetIso wireExact
      endpoint.node
  have portShape := forward.inverseTransportEndpointMap_port_shape targetIso
    wireExact backward targetWire endpoint member
  have sourceRequired := ConcreteDiagram.incident_port_required definitions
    backward.target.val backward.target.property targetWire endpoint member
  unfold PortCorresponds
  refine ⟨mappedNode, ?_⟩
  cases sourceData : backward.target.val.nodes endpoint.node with
  | atom region arguments =>
      rw [sourceData] at mappedData
      rw [ConcreteDiagram.requiredPorts, sourceData] at sourceRequired
      simp only [CNode.rename] at mappedData
      change planned.val.nodes mapped.node = _ at mappedData
      rw [mappedData]
      cases portShape with
      | inl exactPort => exact exactPort
      | inr identityPorts =>
          rcases identityPorts with
            ⟨sourceIndex, _targetIndex, sourcePort, _targetPort⟩
          rw [sourcePort] at sourceRequired
          simp at sourceRequired
  | ref region definition arguments =>
      rw [sourceData] at mappedData
      rw [ConcreteDiagram.requiredPorts, sourceData] at sourceRequired
      simp only [CNode.rename] at mappedData
      change planned.val.nodes mapped.node = _ at mappedData
      rw [mappedData]
      cases portShape with
      | inl exactPort => exact exactPort
      | inr identityPorts =>
          rcases identityPorts with
            ⟨sourceIndex, _targetIndex, sourcePort, _targetPort⟩
          rw [sourcePort] at sourceRequired
          simp at sourceRequired
  | identity region signature arity =>
      rw [sourceData] at mappedData
      rw [ConcreteDiagram.requiredPorts, sourceData] at sourceRequired
      simp only [CNode.rename] at mappedData
      change planned.val.nodes mapped.node = _ at mappedData
      rw [mappedData]
      refine ⟨rfl, rfl, ?_⟩
      cases portShape with
      | inl exactPort =>
          rcases List.mem_map.mp sourceRequired with
            ⟨sourceIndex, _sourceBound, sourcePort⟩
          exact ⟨sourceIndex, sourceIndex, sourcePort.symm,
            exactPort.trans sourcePort.symm⟩
      | inr identityPorts => exact identityPorts

/-- Total concrete isomorphism reconstructed directly from the accepted
extension, its checked inverse drop, and the supplied suffix isomorphism. -/
def inverseTransportIso
    {planned real : CheckedDiagram definitions}
    {forwardOrientation backwardOrientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List planned.val.WireId}
    (forward : AppliedArgExtend planned forwardOrientation forwardWire
      position newArgument attachments)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgDrop real backwardOrientation backwardWire position)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    ConcreteIso backward.target.val planned.val where
  regions := forward.inverseTransportRegionEquiv backward targetIso
  nodes := forward.inverseTransportNodeEquiv backward targetIso
  wires := forward.inverseTransportWireEquiv backward targetIso
  root := forward.inverseTransport_root backward targetIso
  region_table := forward.inverseTransport_region_table backward targetIso
  node_table := forward.inverseTransport_node_table backward targetIso
    wireExact
  wire_signature := forward.inverseTransport_wire_signature backward
    targetIso wireExact
  wire_scope := forward.inverseTransport_wire_scope backward targetIso
    wireExact
  endpointMap := forward.inverseTransportEndpointMap backward targetIso
  endpointInverse := forward.inverseTransportEndpointInverse backward targetIso
  endpointMap_mem := by
    intro targetWire endpoint member
    exact forward.inverseTransportEndpointMap_mem backward targetIso wireExact
      targetWire endpoint member
  endpointInverse_mem := by
    intro targetWire candidate member
    exact forward.inverseTransportEndpointInverse_mem backward targetIso
      wireExact targetWire candidate member
  endpointMap_left_inv := by
    intro targetWire endpoint member
    exact forward.inverseTransportEndpointInverse_map targetIso wireExact
      backward targetWire endpoint member
  endpointMap_right_inv := by
    intro targetWire candidate member
    exact forward.inverseTransportEndpointMap_inverse targetIso wireExact
      backward targetWire candidate member
  endpointMap_corresponds := by
    intro targetWire endpoint member
    exact forward.inverseTransportEndpointMap_corresponds targetIso wireExact
      backward targetWire endpoint member

end AppliedArgExtend

end Arguments

end WirePrimitive

end VisualProof
