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
  boundary : Nat
  identity : host.val.NodeId
  sourceWire : host.val.WireId
  targetWire : host.val.WireId
  identityRegion : host.val.RegionId
  identitySig : Sig
  identityArity : Nat
  distinct : sourceWire ≠ targetWire
  identity_data :
    host.val.nodes identity =
      .identity identityRegion identitySig identityArity
  source_incident :
    sourceWire ∈ host.val.identityIncidentWires identity
  target_incident :
    targetWire ∈ host.val.identityIncidentWires identity
  source_signature : (host.val.wires sourceWire).sig = identitySig
  target_signature : (host.val.wires targetWire).sig = identitySig
  dominates : host.val.Encloses identityRegion site

namespace IdentityRetarget

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
                    { boundary := input.boundary
                      identity := input.identity
                      sourceWire := input.sourceWire
                      targetWire := input.targetWire
                      identityRegion := region
                      identitySig := sig
                      identityArity := arity
                      distinct := distinct
                      identity_data := identityData
                      source_incident := sourceIncident
                      target_incident := targetIncident
                      source_signature := sourceSignature
                      target_signature := targetSignature
                      dominates := dominates }
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
  evidence : IdentityRetarget host site
  attachment :
    attachments[evidence.boundary]? =
      some (evidence.expected direction)

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
    some { evidence := evidence, attachment := attached }
  else
    none

/-- A directionally validated batch with no duplicate boundary positions. -/
structure CheckedIdentityRetargets
    {definitions : List (List Sig)}
    (host : CheckedDiagram definitions)
    (site : host.val.RegionId)
    (direction : IdentityRetargetDirection)
    (attachments : List host.val.WireId) where
  entries :
    List (CheckedIdentityRetarget host site direction attachments)
  positions_nodup :
    (entries.map fun entry => entry.evidence.boundary).Nodup

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
    some { entries := entries, positions_nodup := positionsNodup }
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

/-- The positional attachment tuple consumed by the retarget checker. -/
def concreteAttachmentTargets
    (attachment : ConcreteSpliceAttachment site fragment) :
    List site.complement.val.WireId :=
  List.ofFn attachment.target

@[simp] theorem concreteAttachmentTargets_length
    (attachment : ConcreteSpliceAttachment site fragment) :
    (concreteAttachmentTargets attachment).length =
      fragment.val.boundary.length := by
  simp [concreteAttachmentTargets]

/--
One exact splice attachment and the attachment obtained by applying only the
explicitly checked identity retargets. Both attachments are independently
checked concrete splice inputs; no semantic receipt is supplied by the caller.
-/
structure CheckedIdentityRetargetedSplice
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (site : RemovalResult occurrence)
    (fragment : CheckedOpenDiagram definitions)
    (direction : IdentityRetargetDirection) where
  source : ConcreteSpliceAttachment site fragment
  retargets :
    CheckedIdentityRetargets site.complement site.site direction
      (concreteAttachmentTargets source)
  target : ConcreteSpliceAttachment site fragment
  target_exact :
    ∀ position,
      target.target position =
      retargets.retargetAttachments.get
          ⟨position.val, by
            rw [CheckedIdentityRetargets.retargetAttachments_length]
            rw [concreteAttachmentTargets_length source]
            exact position.isLt⟩

namespace CheckedIdentityRetargetedSplice

/--
At every ordered boundary position, the checked target is either unchanged or
is exactly one checked identity replacement whose expected wire is the source.
-/
theorem target_eq_source_or_entry
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice site fragment direction)
    (position : Fin fragment.val.boundary.length) :
    checked.target.target position = checked.source.target position ∨
      ∃ entry ∈ checked.retargets.entries,
        entry.evidence.boundary = position.val ∧
          checked.source.target position =
            entry.evidence.expected direction ∧
          checked.target.target position =
            entry.evidence.replacement direction := by
  let sourceIndex :
      Fin (concreteAttachmentTargets checked.source).length :=
    ⟨position.val, by
      rw [concreteAttachmentTargets_length]
      exact position.isLt⟩
  have sourceAt :
      (concreteAttachmentTargets checked.source).get sourceIndex =
        checked.source.target position := by
    simp [sourceIndex, concreteAttachmentTargets]
  have classified :=
    checked.retargets.retargetAttachments_get_eq_or_entry sourceIndex
  rw [checked.target_exact position]
  rcases classified with unchanged | changed
  · left
    exact unchanged.trans sourceAt
  · right
    rcases changed with ⟨entry, member, atPosition, targetAt⟩
    have attachedAt :
        (concreteAttachmentTargets checked.source)[position.val]? =
          some (entry.evidence.expected direction) := by
      rw [← atPosition]
      exact entry.attachment
    obtain ⟨bound, attachedValue⟩ :=
      List.getElem?_eq_some_iff.mp attachedAt
    have sourceExpected :
        checked.source.target position =
          entry.evidence.expected direction := by
      have sourceGet :
          (concreteAttachmentTargets checked.source).get sourceIndex =
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
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice site fragment direction)
    (entry :
      CheckedIdentityRetarget site.complement site.site direction
        (concreteAttachmentTargets checked.source))
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
    simpa only [concreteAttachmentTargets_length] using sourceBound
  let position : Fin fragment.val.boundary.length :=
    ⟨entry.evidence.boundary, boundaryBound⟩
  refine ⟨position, rfl, ?_, ?_⟩
  · simpa [position, concreteAttachmentTargets] using sourceAt
  · rw [checked.target_exact position]
    exact
      checked.retargets.retargetAttachments_get_eq_of_mem
        entry member
        (by
          rw [concreteAttachmentTargets_length]
          exact boundaryBound)

end CheckedIdentityRetargetedSplice

/--
Validate a batch against the exact source tuple, apply it positionally, and
recheck the resulting concrete attachment. Invalid structure is refused; no
identity or occurrence is searched for.
-/
def checkIdentityRetargetedSplice
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (site : RemovalResult occurrence)
    (fragment : CheckedOpenDiagram definitions)
    (direction : IdentityRetargetDirection)
    (source : ConcreteSpliceAttachment site fragment)
    (inputs : List (IdentityRetargetInput site.complement)) :
    Option
      (CheckedIdentityRetargetedSplice site fragment direction) := do
  let checked ←
    checkIdentityRetargets site.complement site.site direction
      (concreteAttachmentTargets source) inputs
  let retargeted := checked.retargetAttachments
  have retargetedLength :
      retargeted.length = fragment.val.boundary.length := by
    rw [CheckedIdentityRetargets.retargetAttachments_length]
    exact concreteAttachmentTargets_length source
  let targetAt :
      Fin fragment.val.boundary.length →
        site.complement.val.WireId :=
    fun position =>
      retargeted.get
        ⟨position.val, by
          rw [retargetedLength]
          exact position.isLt⟩
  match accepted :
      checkConcreteSpliceAttachment site fragment targetAt with
  | none => none
  | some target =>
      have targetTable :
          target.target = targetAt :=
        checkConcreteSpliceAttachment_target site fragment targetAt target
          accepted
      some
        { source := source
          retargets := checked
          target := target
          target_exact := by
            intro position
            rw [targetTable]
            }

end VisualProof
