import VisualProof.Rule.WirePrimitive.Arguments

namespace VisualProof

namespace WirePrimitive

namespace Arguments

namespace AppliedArgDrop

/-- Coordinate left after deleting an earlier, distinct position. -/
private def erasePosition (position index : Nat) : Nat :=
  if index < position then index else index - 1

private theorem eraseAt_length_of_lt
    (values : List α) (position : Nat)
    (valid : position < values.length) :
    (ConcreteWirePrimitive.eraseAt values position).length + 1 =
      values.length := by
  induction values generalizing position with
  | nil => simp at valid
  | cons head tail induction =>
      cases position with
      | zero => simp [ConcreteWirePrimitive.eraseAt]
      | succ position =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at valid
          simp [ConcreteWirePrimitive.eraseAt, induction position valid]

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

private theorem eraseAt_getElem?_erasePosition
    (values : List α)
    (position index : Nat)
    (indexBound : index < values.length)
    (different : index ≠ position) :
    (ConcreteWirePrimitive.eraseAt values position)[
        erasePosition position index]? = values[index]? := by
  induction values generalizing position index with
  | nil => simp at indexBound
  | cons head tail induction =>
      cases position with
      | zero =>
          cases index with
          | zero => exact (different rfl).elim
          | succ index =>
              simp only [ConcreteWirePrimitive.eraseAt, erasePosition]
              simp
      | succ position =>
          cases index with
          | zero => simp [ConcreteWirePrimitive.eraseAt, erasePosition]
          | succ index =>
              simp only [List.length_cons, Nat.succ_lt_succ_iff]
                at indexBound
              have step := induction position index indexBound (by omega)
              by_cases before : index < position
              · simpa [ConcreteWirePrimitive.eraseAt, erasePosition,
                  before] using step
              · have after : position < index := by omega
                cases index with
                | zero => omega
                | succ index =>
                    simpa [ConcreteWirePrimitive.eraseAt, erasePosition,
                      before] using step

private theorem insertAt_getElem?_of_ne
    (values : List α)
    (position index : Nat)
    (value : α)
    (positionValid : position ≤ values.length)
    (indexBound : index < values.length + 1)
    (different : index ≠ position) :
    (ConcreteWirePrimitive.insertAt values position value)[index]? =
      values[erasePosition position index]? := by
  induction values generalizing position index with
  | nil =>
      simp only [List.length_nil] at positionValid indexBound
      have positionZero : position = 0 := by omega
      have indexZero : index = 0 := by omega
      exact (different (indexZero.trans positionZero.symm)).elim
  | cons head tail induction =>
      cases position with
      | zero =>
          cases index with
          | zero => exact (different rfl).elim
          | succ index =>
              simp [ConcreteWirePrimitive.insertAt, erasePosition]
      | succ position =>
          cases index with
          | zero => simp [ConcreteWirePrimitive.insertAt, erasePosition]
          | succ index =>
              simp only [List.length_cons, Nat.succ_le_succ_iff]
                at positionValid
              simp only [List.length_cons, Nat.succ_lt_succ_iff,
                Nat.succ_add] at indexBound
              have step := induction position index positionValid indexBound
                (by omega)
              by_cases before : index < position
              · simpa [ConcreteWirePrimitive.insertAt, erasePosition,
                  before] using step
              · have after : position < index := by omega
                cases index with
                | zero => omega
                | succ index =>
                    simpa [ConcreteWirePrimitive.insertAt, erasePosition,
                      before] using step

/-- Pair-specific endpoint transport. Rebuilt application nodes are related
directly in their restored argument coordinate; retained nodes compose the
unchanged construction transports with the supplied suffix isomorphism. -/
def inverseTransportEndpointMap
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
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
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (targetWire : backward.target.val.WireId)
    (endpoint : CEndpoint planned.val.nodeCount) :
    CEndpoint backward.target.val.nodeCount :=
  if generated : endpoint.node ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.sourceSites then
    ⟨(forward.inverseTransportNodeEquiv backward targetIso).symm
        endpoint.node, endpoint.port⟩
  else
    let realWire := backward.wireEquiv.symm targetWire
    let middleEndpoint : CEndpoint forward.target.val.nodeCount :=
      ⟨forward.nodeEquiv endpoint.node, endpoint.port⟩
    let realEndpoint := targetIso.endpointInverse realWire middleEndpoint
    ⟨backward.nodeEquiv realEndpoint.node, realEndpoint.port⟩

/-- On retained nodes, the pair transport is exactly suffix composition and
therefore preserves incidence without any argument-coordinate case. -/
theorem inverseTransportEndpointMap_mem_retained
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
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

/-- The endpoint introduced only by the inverse extension maps directly to
the construction-owned endpoint erased by the forward drop. -/
theorem inverseTransportEndpointMap_inserted
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument (forward.inverseAttachments targetIso wireExact))
    (argumentExact :
      forward.sourceArgumentList[position]? = some newArgument)
    (site : Fin backward.sourceSites.sites.length) :
    let attachment :=
      ((forward.inverseAttachments targetIso wireExact)[site.val]?).getD
        backwardWire
    let targetWire := backward.wireEquiv attachment
    let endpoint : CEndpoint backward.target.val.nodeCount :=
      ⟨backward.targetNode site, .arg position⟩
    forward.inverseTransportEndpointMap backward targetIso targetWire endpoint =
      ⟨(forward.sourceSites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node, .arg position⟩ ∧
    forward.inverseTransportWireEquiv backward targetIso targetWire =
      ((forward.sourceSites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).arguments[position]?).getD forwardWire := by
  dsimp only
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
    rw [show backward.nodeEquiv.symm (backward.targetNode site) =
      realNode from backwardInverse, dif_pos generated]
    congr 1
    exact forward.inverseTransport_targetNode backward targetIso
      wireExact site
  · exact forward.inverseTransport_insertedWire targetIso wireExact
      backward site

/-- Rebuilt head endpoints map directly to the original planned heads. -/
theorem inverseTransportEndpointMap_head
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
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

/-- Every rebuilt noninserted argument endpoint maps at the same restored
argument coordinate, and its construction-owned wire maps to the exact
planned attachment at that coordinate. -/
theorem inverseTransportEndpointMap_argument
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    {attachments : List real.val.WireId}
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument attachments)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (argumentExact :
      forward.sourceArgumentList[position]? = some newArgument)
    (site : Fin backward.sourceSites.sites.length)
    (index : Nat)
    (indexBound : index < backward.targetArgumentList.length)
    (different : index ≠ position) :
    let backwardSite := backward.sourceSites.sites.get site
    let sourcePosition := erasePosition position index
    let realAttachment :=
      (backwardSite.arguments[sourcePosition]?).getD backwardWire
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
  have argumentBound : position < forward.sourceArgumentList.length :=
    (List.getElem?_eq_some_iff.mp argumentExact).choose
  have erasedLength := eraseAt_length_of_lt forward.sourceArgumentList
    position argumentBound
  have sourceArguments := forward.inverseSourceArguments_exact backward
    targetIso wireExact
  rw [forward.targetArguments_exact] at sourceArguments
  have positionValid : position ≤ backward.sourceArgumentList.length := by
    rw [sourceArguments]
    omega
  have targetLength : backward.targetArgumentList.length =
      backward.sourceArgumentList.length + 1 := by
    unfold AppliedArgExtend.targetArgumentList
    rw [backward.targetArguments_exact,
      insertAt_length_of_le backward.sourceArgumentList position newArgument
        positionValid]
  have indexLength := indexBound
  have sourcePositionBound : erasePosition position index <
      backward.sourceArgumentList.length := by
    rw [targetLength] at indexLength
    unfold erasePosition
    split <;> omega
  have backwardSiteLength : backwardSite.arguments.length =
      backward.sourceArgumentList.length := by
    exact backwardSite.arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          backward.sourceArgumentList backward.sourceWire_signature
          backwardSite))
  have backwardSitePositionBound : erasePosition position index <
      backwardSite.arguments.length := by
    rw [backwardSiteLength]
    exact sourcePositionBound
  have backwardAttachmentGet :
      backwardSite.arguments[erasePosition position index]? =
        some ((backwardSite.arguments[erasePosition position index]?).getD
          backwardWire) := by
    rw [List.getElem?_eq_getElem (by
      exact backwardSitePositionBound)]
    simp
  let realAttachment :=
    (backwardSite.arguments[erasePosition position index]?).getD backwardWire
  have insertedAtIndex :
      (ConcreteWirePrimitive.insertAt backwardSite.arguments position
        ((attachments[site.val]?).getD backwardWire))[index]? =
        some realAttachment := by
    rw [insertAt_getElem?_of_ne backwardSite.arguments position index
      ((attachments[site.val]?).getD backwardWire)]
    · exact backwardAttachmentGet
    · rw [backwardSiteLength]
      exact positionValid
    · rw [backwardSiteLength, ← targetLength]
      exact indexBound
    · exact different
  have backwardNodeData := backwardSite.node_data
  have middleOwner := targetIso.atom_owner_forward real.property
    forward.target.property backwardNodeData
      (backwardSite.argument_owner (erasePosition position index)
        backwardSitePositionBound)
  have realAttachmentExact :
      backwardSite.arguments[erasePosition position index]'
        backwardSitePositionBound = realAttachment := by
    simp [realAttachment, List.getElem?_eq_getElem,
      backwardSitePositionBound]
  rw [realAttachmentExact] at middleOwner
  let plannedAttachment :=
    (plannedSite.arguments[index]?).getD forwardWire
  have plannedSiteLength : plannedSite.arguments.length =
      forward.sourceArgumentList.length := by
    exact plannedSite.arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          forward.sourceArgumentList forward.sourceWire_signature
          plannedSite))
  have plannedArgumentBound : index < plannedSite.arguments.length := by
    have restored := forward.inverseTargetArguments_exact backward targetIso
      wireExact argumentExact
    rw [plannedSiteLength, ← restored]
    exact indexBound
  have plannedAttachmentGet : plannedSite.arguments[index]? =
      some plannedAttachment := by
    simp [plannedAttachment, List.getElem?_eq_getElem, plannedArgumentBound]
  have erasedPlannedGet :
      (ConcreteWirePrimitive.eraseAt plannedSite.arguments position)[
          erasePosition position index]? =
        some plannedAttachment := by
    rw [eraseAt_getElem?_erasePosition plannedSite.arguments position index
      plannedArgumentBound different]
    exact plannedAttachmentGet
  have forwardTargetBound : erasePosition position index <
      forward.targetArgumentList.length := by
    unfold AppliedArgDrop.targetArgumentList
    rw [forward.targetArguments_exact]
    have plannedPositionBound :=
      (List.getElem?_eq_some_iff.mp erasedPlannedGet).choose
    have plannedPositionValid : position < plannedSite.arguments.length := by
      rw [plannedSiteLength]
      exact argumentBound
    have plannedErasedLength := eraseAt_length_of_lt plannedSite.arguments
      position plannedPositionValid
    omega
  have forwardOwner := forward.generatedArgument_endpointOwner_of_selected
    plannedPosition (erasePosition position index) forwardTargetBound
      plannedAttachment erasedPlannedGet
  have middleNode := forward.inverseTransport_middleNode backward targetIso
    wireExact site
  change targetIso.nodes backwardSite.node =
    forward.targetNode plannedPosition at middleNode
  rw [middleNode] at middleOwner
  have middleWire : targetIso.wires realAttachment =
      forward.wireEquiv plannedAttachment :=
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
      exact forward.wireEquiv.left_inv plannedAttachment
    · exact backward.generatedArgument_endpointOwner_of_selected site index
        indexBound realAttachment insertedAtIndex

/-- The pair-specific endpoint map preserves incidence on every inverse
extension target wire. -/
theorem inverseTransportEndpointMap_mem
    {planned real : CheckedDiagram definitions}
    {orientation : Orientation}
    {forwardWire : planned.val.WireId}
    {position : Nat}
    (forward : AppliedArgDrop planned orientation forwardWire position)
    {backwardWire : real.val.WireId}
    {newArgument : Sig}
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (backward : AppliedArgExtend real orientation backwardWire position
      newArgument (forward.inverseAttachments targetIso wireExact))
    (argumentExact :
      forward.sourceArgumentList[position]? = some newArgument)
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
        have generatedOwner := backward.generatedHead_endpointOwner site
        have targetWireExact : targetWire = backward.targetWire :=
          Option.some.inj (actualOwner.symm.trans generatedOwner)
        subst targetWire
        have transported := forward.inverseTransportEndpointMap_head backward
          targetIso wireExact site
        rw [transported.1, transported.2]
        exact ConcreteDiagram.endpointOwner?_incident planned.val
          ⟨plannedSite.node, .head⟩ forwardWire plannedSite.endpoint_owner
    | arg index =>
        have indexBound := backward.generatedArgument_bound site index required
        by_cases inserted : index = position
        · subst index
          have argumentBound : position <
              forward.sourceArgumentList.length :=
            (List.getElem?_eq_some_iff.mp argumentExact).choose
          have erasedLength := eraseAt_length_of_lt
            forward.sourceArgumentList position argumentBound
          have sourceArguments := forward.inverseSourceArguments_exact
            backward targetIso wireExact
          rw [forward.targetArguments_exact] at sourceArguments
          have positionValid : position ≤
              backward.sourceArgumentList.length := by
            rw [sourceArguments]
            omega
          let attachment :=
            ((forward.inverseAttachments targetIso wireExact)[site.val]?).getD
              backwardWire
          have generatedOwner := backward.generatedInserted_endpointOwner
            positionValid site
          have targetWireExact : targetWire =
              backward.wireEquiv attachment :=
            Option.some.inj (actualOwner.symm.trans generatedOwner)
          subst targetWire
          have transported := forward.inverseTransportEndpointMap_inserted
            targetIso wireExact backward argumentExact site
          rw [transported.1, transported.2]
          have plannedSiteLength : plannedSite.arguments.length =
              forward.sourceArgumentList.length := by
            exact plannedSite.arguments_length.trans
              (congrArg List.length
                (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
                  forward.sourceArgumentList forward.sourceWire_signature
                  plannedSite))
          have plannedBound : position < plannedSite.arguments.length := by
            rw [plannedSiteLength]
            exact argumentBound
          have owner := plannedSite.argument_owner position plannedBound
          have attachmentExact :
              plannedSite.arguments[position]'plannedBound =
                (plannedSite.arguments[position]?).getD forwardWire := by
            simp [plannedBound]
          rw [attachmentExact] at owner
          exact ConcreteDiagram.endpointOwner?_incident planned.val
            ⟨plannedSite.node, .arg position⟩
            ((plannedSite.arguments[position]?).getD forwardWire) owner
        · have transported := forward.inverseTransportEndpointMap_argument
            backward targetIso wireExact argumentExact site index indexBound
              inserted
          let realAttachment :=
            (backwardSite.arguments[erasePosition position index]?).getD
              backwardWire
          let plannedAttachment :=
            (plannedSite.arguments[index]?).getD forwardWire
          have targetWireExact : targetWire =
              backward.wireEquiv realAttachment :=
            Option.some.inj (actualOwner.symm.trans transported.2.2)
          subst targetWire
          rw [transported.1, transported.2.1]
          have restored := forward.inverseTargetArguments_exact backward
            targetIso wireExact argumentExact
          have plannedSiteLength : plannedSite.arguments.length =
              forward.sourceArgumentList.length := by
            exact plannedSite.arguments_length.trans
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
        exact (backward.generatedIdentity_not_required site index required).elim

end AppliedArgDrop

end Arguments

end WirePrimitive

end VisualProof
