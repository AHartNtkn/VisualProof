import VisualProof.Diagram.Concrete.IdentityIncidence
import VisualProof.Diagram.Concrete.Subgraph.Splice

namespace VisualProof

/-- Durable equality evidence is always oriented outer source to inner target. -/
inductive IdentityRetargetDirection
  | iteration
  | deiteration
  deriving Repr, DecidableEq

/-- Serialized structural input before the checker derives its receipts. -/
structure IdentityRetargetInput
    {definitions : List (List Sig)}
    (host : CheckedDiagram definitions) where
  boundary : Nat
  identity : host.val.NodeId
  sourceWire : host.val.WireId
  targetWire : host.val.WireId

/--
Boundary-independent structural equality evidence.

The evidence keeps one stable outer-source → inner-target orientation. A
directional attachment checker separately validates iteration against the
source wire and deiteration against the target wire.
-/
structure IdentityRetarget
    {definitions : List (List Sig)}
    (host : CheckedDiagram definitions)
    (site : host.val.RegionId) : Type where
  private mk ::
  private boundaryValue : Nat
  private identityValue : host.val.NodeId
  private sourceWireValue : host.val.WireId
  private targetWireValue : host.val.WireId
  private identityRegionValue : host.val.RegionId
  private identitySigValue : Sig
  private identityArityValue : Nat
  private distinctProof : sourceWireValue ≠ targetWireValue
  private identityDataProof :
    host.val.nodes identityValue =
      .identity identityRegionValue identitySigValue identityArityValue
  private sourceIncidentProof :
    sourceWireValue ∈ host.val.identityIncidentWires identityValue
  private targetIncidentProof :
    targetWireValue ∈ host.val.identityIncidentWires identityValue
  private sourceSignatureProof :
    (host.val.wires sourceWireValue).sig = identitySigValue
  private targetSignatureProof :
    (host.val.wires targetWireValue).sig = identitySigValue
  private dominatesProof : host.val.Encloses identityRegionValue site

namespace IdentityRetarget

def boundary (retarget : IdentityRetarget host site) : Nat :=
  retarget.boundaryValue

def identity (retarget : IdentityRetarget host site) : host.val.NodeId :=
  retarget.identityValue

def sourceWire (retarget : IdentityRetarget host site) : host.val.WireId :=
  retarget.sourceWireValue

def targetWire (retarget : IdentityRetarget host site) : host.val.WireId :=
  retarget.targetWireValue

def identityRegion (retarget : IdentityRetarget host site) :
    host.val.RegionId :=
  retarget.identityRegionValue

def identitySig (retarget : IdentityRetarget host site) : Sig :=
  retarget.identitySigValue

def identityArity (retarget : IdentityRetarget host site) : Nat :=
  retarget.identityArityValue

theorem distinct (retarget : IdentityRetarget host site) :
    retarget.sourceWire ≠ retarget.targetWire :=
  retarget.distinctProof

theorem identity_data (retarget : IdentityRetarget host site) :
    host.val.nodes retarget.identity =
      .identity retarget.identityRegion retarget.identitySig
        retarget.identityArity :=
  retarget.identityDataProof

theorem source_incident (retarget : IdentityRetarget host site) :
    retarget.sourceWire ∈
      host.val.identityIncidentWires retarget.identity :=
  retarget.sourceIncidentProof

theorem target_incident (retarget : IdentityRetarget host site) :
    retarget.targetWire ∈
      host.val.identityIncidentWires retarget.identity :=
  retarget.targetIncidentProof

theorem source_signature (retarget : IdentityRetarget host site) :
    (host.val.wires retarget.sourceWire).sig = retarget.identitySig :=
  retarget.sourceSignatureProof

theorem target_signature (retarget : IdentityRetarget host site) :
    (host.val.wires retarget.targetWire).sig = retarget.identitySig :=
  retarget.targetSignatureProof

theorem dominates (retarget : IdentityRetarget host site) :
    host.val.Encloses retarget.identityRegion site :=
  retarget.dominatesProof

def expected
    (direction : IdentityRetargetDirection)
    (retarget : IdentityRetarget host site) : host.val.WireId :=
  match direction with
  | .iteration => retarget.sourceWire
  | .deiteration => retarget.targetWire

def replacement
    (direction : IdentityRetargetDirection)
    (retarget : IdentityRetarget host site) : host.val.WireId :=
  match direction with
  | .iteration => retarget.targetWire
  | .deiteration => retarget.sourceWire

end IdentityRetarget

/-- Validate the boundary-independent identity, incidence, type, and scope gates. -/
def checkIdentityRetargetEvidence
    {definitions : List (List Sig)}
    (host : CheckedDiagram definitions)
    (site : host.val.RegionId)
    (input : IdentityRetargetInput host) :
    Option (IdentityRetarget host site) := by
  if distinct : input.sourceWire ≠ input.targetWire then
    match identityData : host.val.nodes input.identity with
    | .identity region sig arity =>
        if sourceIncident :
            input.sourceWire ∈
              host.val.identityIncidentWires input.identity then
          if targetIncident :
              input.targetWire ∈
                host.val.identityIncidentWires input.identity then
            if sourceSignature :
                (host.val.wires input.sourceWire).sig = sig then
              if targetSignature :
                  (host.val.wires input.targetWire).sig = sig then
                if dominates : host.val.Encloses region site then
                  exact some
                    (IdentityRetarget.mk input.boundary input.identity
                      input.sourceWire input.targetWire region sig arity
                      distinct identityData sourceIncident targetIncident
                      sourceSignature targetSignature dominates)
                else
                  exact none
              else
                exact none
            else
              exact none
          else
            exact none
        else
          exact none
    | .atom _ _ => exact none
    | .ref _ _ _ => exact none
  else
    exact none

/-- One stable retarget validated against the attachments for one direction. -/
structure CheckedIdentityRetarget
    {definitions : List (List Sig)}
    (host : CheckedDiagram definitions)
    (site : host.val.RegionId)
    (direction : IdentityRetargetDirection)
    (attachments : List host.val.WireId) where
  private mk ::
  private evidenceValue : IdentityRetarget host site
  private attachmentProof :
    attachments[evidenceValue.boundary]? =
      some (evidenceValue.expected direction)

namespace CheckedIdentityRetarget

def evidence
    (checked : CheckedIdentityRetarget host site direction attachments) :
    IdentityRetarget host site :=
  checked.evidenceValue

theorem attachment
    (checked : CheckedIdentityRetarget host site direction attachments) :
    attachments[checked.evidence.boundary]? =
      some (checked.evidence.expected direction) :=
  checked.attachmentProof

end CheckedIdentityRetarget

/--
Validate one supplied retarget at exactly its named boundary position.
No occurrence, identity, or replacement is searched for.
-/
def checkIdentityRetarget
    {definitions : List (List Sig)}
    (host : CheckedDiagram definitions)
    (site : host.val.RegionId)
    (direction : IdentityRetargetDirection)
    (attachments : List host.val.WireId)
    (input : IdentityRetargetInput host) :
    Option
      (CheckedIdentityRetarget host site direction attachments) := do
  let evidence ← checkIdentityRetargetEvidence host site input
  if attached :
      attachments[evidence.boundary]? =
        some (evidence.expected direction) then
    some (CheckedIdentityRetarget.mk evidence attached)
  else
    none

/-- A directionally validated batch with no duplicate boundary positions. -/
structure CheckedIdentityRetargets
    {definitions : List (List Sig)}
    (host : CheckedDiagram definitions)
    (site : host.val.RegionId)
    (direction : IdentityRetargetDirection)
    (attachments : List host.val.WireId) where
  private mk ::
  private entriesValue :
    List (CheckedIdentityRetarget host site direction attachments)
  private positionsNodupProof :
    (entriesValue.map fun entry => entry.evidence.boundary).Nodup

namespace CheckedIdentityRetargets

def entries
    (checked :
      CheckedIdentityRetargets host site direction attachments) :
    List (CheckedIdentityRetarget host site direction attachments) :=
  checked.entriesValue

theorem positions_nodup
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {site : host.val.RegionId}
    {direction : IdentityRetargetDirection}
    {attachments : List host.val.WireId}
    (checked :
      CheckedIdentityRetargets host site direction attachments) :
    (checked.entries.map fun entry => entry.evidence.boundary).Nodup :=
  checked.positionsNodupProof

end CheckedIdentityRetargets

/-- Validate every explicit retarget and reject duplicate boundary positions. -/
def checkIdentityRetargets
    {definitions : List (List Sig)}
    (host : CheckedDiagram definitions)
    (site : host.val.RegionId)
    (direction : IdentityRetargetDirection)
    (attachments : List host.val.WireId)
    (inputs : List (IdentityRetargetInput host)) :
    Option
      (CheckedIdentityRetargets host site direction attachments) := do
  let entries ← inputs.mapM fun input =>
    checkIdentityRetarget host site direction attachments input
  if positionsNodup :
      (entries.map fun entry => entry.evidence.boundary).Nodup then
    some (CheckedIdentityRetargets.mk entries positionsNodup)
  else
    none

namespace CheckedIdentityRetargets

private def replacementAt?
    (checked :
      CheckedIdentityRetargets host site direction attachments)
    (index : Nat) : Option host.val.WireId :=
  (checked.entries.find?
    (fun entry => decide (entry.evidence.boundary = index))).map
    (fun entry => entry.evidence.replacement direction)

private theorem entry_eq_of_boundary_eq
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {site : host.val.RegionId}
    {direction : IdentityRetargetDirection}
    {attachments : List host.val.WireId}
    (entries :
      List (CheckedIdentityRetarget host site direction attachments))
    (positionsNodup :
      (entries.map fun entry => entry.evidence.boundary).Nodup)
    {left right :
      CheckedIdentityRetarget host site direction attachments}
    (leftMember : left ∈ entries)
    (rightMember : right ∈ entries)
    (sameBoundary :
      left.evidence.boundary = right.evidence.boundary) :
    left = right := by
  induction entries generalizing left right with
  | nil => simp at leftMember
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at positionsNodup
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with sameLeft | leftTail
      · subst left
        rcases rightMember with sameRight | rightTail
        · exact sameRight.symm
        · have forbidden :
              head.evidence.boundary ∈
                tail.map fun entry => entry.evidence.boundary :=
            List.mem_map.mpr
              ⟨right, rightTail, sameBoundary.symm⟩
          exact (positionsNodup.1 forbidden).elim
      · rcases rightMember with sameRight | rightTail
        · subst right
          have forbidden :
              head.evidence.boundary ∈
                tail.map fun entry => entry.evidence.boundary :=
            List.mem_map.mpr
              ⟨left, leftTail, sameBoundary⟩
          exact (positionsNodup.1 forbidden).elim
        · exact
            induction positionsNodup.2 leftTail rightTail sameBoundary

/--
Apply the checked replacements pointwise. Untouched attachment positions stay
in place, so list length and ordering are preserved.
-/
def retargetAttachments
    (checked :
      CheckedIdentityRetargets host site direction attachments) :
    List host.val.WireId :=
  attachments.mapIdx fun index wire =>
    (checked.replacementAt? index).getD wire

@[simp] theorem retargetAttachments_length
    (checked :
      CheckedIdentityRetargets host site direction attachments) :
    checked.retargetAttachments.length = attachments.length := by
  simp [retargetAttachments]

/--
Every output position is either untouched or is exactly the replacement owned
by the unique checked entry found at that position.
-/
theorem retargetAttachments_get_eq_or_entry
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {site : host.val.RegionId}
    {direction : IdentityRetargetDirection}
    {attachments : List host.val.WireId}
    (checked :
      CheckedIdentityRetargets host site direction attachments)
    (position : Fin attachments.length) :
    checked.retargetAttachments.get
          ⟨position.val, by
            simpa only [retargetAttachments_length] using
              position.isLt⟩ =
        attachments.get position ∨
      ∃ entry ∈ checked.entries,
        entry.evidence.boundary = position.val ∧
          checked.retargetAttachments.get
              ⟨position.val, by
                simpa only [retargetAttachments_length] using
                  position.isLt⟩ =
            entry.evidence.replacement direction := by
  simp only [retargetAttachments, List.get_eq_getElem,
    List.getElem_mapIdx]
  unfold replacementAt?
  cases found :
      checked.entries.find?
        (fun entry => decide (entry.evidence.boundary = position.val)) with
  | none =>
      left
      simp
  | some entry =>
      right
      have member : entry ∈ checked.entries :=
        List.mem_of_find?_eq_some found
      have atPosition :
          entry.evidence.boundary = position.val :=
        of_decide_eq_true
          (List.find?_some
            (p := fun candidate :
                CheckedIdentityRetarget host site direction attachments =>
              decide (candidate.evidence.boundary = position.val))
            found)
      exact ⟨entry, member, atPosition, by simp⟩

/--
A checked entry owns its named output position: lookup at that position is
exactly its replacement. The no-duplicate receipt makes the `find?` choice
proof-independent.
-/
theorem retargetAttachments_get_eq_of_mem
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions}
    {site : host.val.RegionId}
    {direction : IdentityRetargetDirection}
    {attachments : List host.val.WireId}
    (checked :
      CheckedIdentityRetargets host site direction attachments)
    (entry :
      CheckedIdentityRetarget host site direction attachments)
    (member : entry ∈ checked.entries)
    (bound : entry.evidence.boundary < attachments.length) :
    checked.retargetAttachments.get
          ⟨entry.evidence.boundary, by
            simpa only [retargetAttachments_length] using bound⟩ =
        entry.evidence.replacement direction := by
  simp only [retargetAttachments, List.get_eq_getElem,
    List.getElem_mapIdx]
  unfold replacementAt?
  cases found :
      checked.entries.find?
        (fun candidate =>
          decide
            (candidate.evidence.boundary =
              entry.evidence.boundary)) with
  | none =>
      have rejected :=
        (List.find?_eq_none.mp found) entry member
      simp at rejected
  | some selected =>
      have selectedMember : selected ∈ checked.entries :=
        List.mem_of_find?_eq_some found
      have selectedBoundary :
          selected.evidence.boundary =
            entry.evidence.boundary :=
        of_decide_eq_true
          (List.find?_some
            (p := fun candidate :
                CheckedIdentityRetarget host site direction attachments =>
              decide
                (candidate.evidence.boundary =
                  entry.evidence.boundary))
            found)
      have selectedExact : selected = entry :=
        entry_eq_of_boundary_eq checked.entries
          checked.positions_nodup selectedMember member selectedBoundary
      subst selected
      simp

end CheckedIdentityRetargets

/-- The ordered positional tuple consumed by the identity-retarget checker. -/
def orderedAttachmentTuple
    (attachment : ConcreteSpliceAttachment base site fragment) :
    List base.val.WireId :=
  List.ofFn attachment.target

@[simp] theorem orderedAttachmentTuple_length
    (attachment : ConcreteSpliceAttachment base site fragment) :
    (orderedAttachmentTuple attachment).length =
      fragment.val.boundary.length := by
  simp [orderedAttachmentTuple]

/--
One exact splice attachment and the attachment obtained by applying only the
explicitly checked identity retargets. Both attachments are independently
checked concrete splice inputs; no semantic receipt is supplied by the caller.
-/
structure CheckedIdentityRetargetedSplice
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId)
    (fragment : CheckedOpenDiagram definitions)
    (direction : IdentityRetargetDirection) where
  private mk ::
  source : ConcreteSpliceAttachment base site fragment
  retargets :
    CheckedIdentityRetargets base site direction
      (orderedAttachmentTuple source)
  target : ConcreteSpliceAttachment base site fragment
  private targetExactProof :
    ∀ position,
      target.target position =
      retargets.retargetAttachments.get
          ⟨position.val, by
            rw [CheckedIdentityRetargets.retargetAttachments_length]
            rw [orderedAttachmentTuple_length source]
            exact position.isLt⟩

namespace CheckedIdentityRetargetedSplice

theorem target_exact
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice base site fragment direction)
    (position : Fin fragment.val.boundary.length) :
    checked.target.target position =
      checked.retargets.retargetAttachments.get
        ⟨position.val, by
          rw [CheckedIdentityRetargets.retargetAttachments_length]
          rw [orderedAttachmentTuple_length checked.source]
          exact position.isLt⟩ :=
  checked.targetExactProof position

/--
At every ordered boundary position, the checked target is either unchanged or
is exactly one checked identity replacement whose expected wire is the source.
-/
theorem target_eq_source_or_entry
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice base site fragment direction)
    (position : Fin fragment.val.boundary.length) :
    checked.target.target position = checked.source.target position ∨
      ∃ entry ∈ checked.retargets.entries,
        entry.evidence.boundary = position.val ∧
          checked.source.target position =
            entry.evidence.expected direction ∧
          checked.target.target position =
            entry.evidence.replacement direction := by
  let sourceIndex :
      Fin (orderedAttachmentTuple checked.source).length :=
    ⟨position.val, by
      rw [orderedAttachmentTuple_length]
      exact position.isLt⟩
  have sourceAt :
      (orderedAttachmentTuple checked.source).get sourceIndex =
        checked.source.target position := by
    simp [sourceIndex, orderedAttachmentTuple]
  have classified :=
    checked.retargets.retargetAttachments_get_eq_or_entry sourceIndex
  rw [checked.target_exact position]
  rcases classified with unchanged | changed
  · left
    exact unchanged.trans sourceAt
  · right
    rcases changed with ⟨entry, member, atPosition, targetAt⟩
    have attachedAt :
        (orderedAttachmentTuple checked.source)[position.val]? =
          some (entry.evidence.expected direction) := by
      rw [← atPosition]
      exact entry.attachment
    obtain ⟨bound, attachedValue⟩ :=
      List.getElem?_eq_some_iff.mp attachedAt
    have sourceExpected :
        checked.source.target position =
          entry.evidence.expected direction := by
      have sourceGet :
          (orderedAttachmentTuple checked.source).get sourceIndex =
            entry.evidence.expected direction := by
        simpa [sourceIndex, List.get_eq_getElem] using attachedValue
      exact sourceAt.symm.trans sourceGet
    exact
      ⟨entry, member, atPosition, sourceExpected,
        targetAt.trans rfl⟩

/--
Every checked batch entry recovers its own in-bounds boundary position and the
exact source-to-replacement pair at that position.
-/
theorem entry_position_exact
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice base site fragment direction)
    (entry :
      CheckedIdentityRetarget base site direction
        (orderedAttachmentTuple checked.source))
    (member : entry ∈ checked.retargets.entries) :
    ∃ position : Fin fragment.val.boundary.length,
      entry.evidence.boundary = position.val ∧
        checked.source.target position =
          entry.evidence.expected direction ∧
        checked.target.target position =
          entry.evidence.replacement direction := by
  obtain ⟨sourceBound, sourceAt⟩ :=
    List.getElem?_eq_some_iff.mp entry.attachment
  have boundaryBound :
      entry.evidence.boundary < fragment.val.boundary.length := by
    simpa only [orderedAttachmentTuple_length] using sourceBound
  let position : Fin fragment.val.boundary.length :=
    ⟨entry.evidence.boundary, boundaryBound⟩
  refine ⟨position, rfl, ?_, ?_⟩
  · simpa [position, orderedAttachmentTuple] using sourceAt
  · rw [checked.target_exact position]
    exact
      checked.retargets.retargetAttachments_get_eq_of_mem
        entry member
        (by
          rw [orderedAttachmentTuple_length]
          exact boundaryBound)

end CheckedIdentityRetargetedSplice

/--
Validate a batch against the exact source tuple, apply it positionally, and
recheck the resulting concrete attachment. Invalid structure is refused; no
identity or occurrence is searched for.
-/
def checkIdentityRetargetedSplice
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId)
    (fragment : CheckedOpenDiagram definitions)
    (direction : IdentityRetargetDirection)
    (source : ConcreteSpliceAttachment base site fragment)
    (inputs : List (IdentityRetargetInput base)) :
    Option
      (CheckedIdentityRetargetedSplice base site fragment direction) := do
  let checked ←
    checkIdentityRetargets base site direction
      (orderedAttachmentTuple source) inputs
  let retargeted := checked.retargetAttachments
  have retargetedLength :
      retargeted.length = fragment.val.boundary.length := by
    rw [CheckedIdentityRetargets.retargetAttachments_length]
    exact orderedAttachmentTuple_length source
  let targetAt :
      Fin fragment.val.boundary.length →
        base.val.WireId :=
    fun position =>
      retargeted.get
        ⟨position.val, by
          rw [retargetedLength]
          exact position.isLt⟩
  match accepted :
      checkConcreteSpliceAttachment base site fragment targetAt with
  | none => none
  | some target =>
      have targetTable :
          target.target = targetAt :=
        checkConcreteSpliceAttachment_target base site fragment targetAt
          target accepted
      some
        (CheckedIdentityRetargetedSplice.mk source checked target (by
          intro position
          rw [targetTable]))

end VisualProof
