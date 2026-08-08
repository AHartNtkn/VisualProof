import VisualProof.Refinement.Implementation.IterationExtractionSelected
import VisualProof.Refinement.Implementation.IterationRoute

namespace VisualProof.Refinement.Implementation.IterationSourceFactor

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationPartition
open VisualProof.Refinement.Implementation.IterationRoute

/-- Anchor-local wires retained by the source context.  The explicit block is
owned by the selected factor instead. -/
def retainedAnchorWires
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) : List (Fin input.wireCount) :=
  (Concrete.Elaboration.exactScopeWires input selection.val.anchor).filter
    (fun wire => !(decide (wire ∈ selection.val.explicitWires)))

/-- Complete outer context of the selected factor: inherited wires followed
by anchor-local wires not explicitly owned by the selection. -/
def retainedContext
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    Concrete.Elaboration.WireContext input :=
  inherited ++ retainedAnchorWires input selection

theorem explicitWire_mem_exactScopeWires
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    {wire : Fin input.wireCount}
    (member : wire ∈ selection.val.explicitWires) :
    wire ∈ Concrete.Elaboration.exactScopeWires input
      selection.val.anchor := by
  rw [Concrete.Elaboration.mem_exactScopeWires]
  exact selection.property.explicitWires_at_anchor wire member

theorem retainedAnchorWires_nodup
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (retainedAnchorWires input selection).Nodup := by
  exact (Concrete.Elaboration.exactScopeWires_nodup input
    selection.val.anchor).filter _

@[simp] theorem mem_retainedAnchorWires
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wire : Fin input.wireCount) :
    wire ∈ retainedAnchorWires input selection ↔
      (input.wires wire).scope = selection.val.anchor ∧
        wire ∉ selection.val.explicitWires := by
  simp [retainedAnchorWires]

private theorem perm_of_nodup_and_mem_iff
    {values other : List α} [BEq α] [LawfulBEq α]
    (valuesNodup : values.Nodup) (otherNodup : other.Nodup)
    (members : ∀ value, value ∈ values ↔ value ∈ other) :
    values.Perm other := by
  rw [List.perm_iff_count]
  intro value
  rw [valuesNodup.count, otherNodup.count]
  by_cases member : value ∈ values
  · have otherMember : value ∈ other := (members value).1 member
    simp [member, otherMember]
  · have otherNotMember : value ∉ other :=
      fun present => member ((members value).2 present)
    simp [member, otherNotMember]

theorem selectedExplicitFilter_perm
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    ((Concrete.Elaboration.exactScopeWires input selection.val.anchor).filter
      (fun wire => decide (wire ∈ selection.val.explicitWires))).Perm
      selection.val.explicitWires := by
  apply perm_of_nodup_and_mem_iff
  · exact (Concrete.Elaboration.exactScopeWires_nodup input
      selection.val.anchor).filter _
  · exact selection.property.explicitWires_nodup
  · intro wire
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun member => member.2
    · intro member
      exact ⟨explicitWire_mem_exactScopeWires input selection member, member⟩

theorem retainedAnchorWires_append_explicit_perm
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (retainedAnchorWires input selection ++
      selection.val.explicitWires).Perm
      (Concrete.Elaboration.exactScopeWires input selection.val.anchor) := by
  let exact := Concrete.Elaboration.exactScopeWires input selection.val.anchor
  let selected := exact.filter
    (fun wire => decide (wire ∈ selection.val.explicitWires))
  have partition : (retainedAnchorWires input selection ++ selected).Perm exact := by
    have split := List.filter_append_perm
      (fun wire => decide (wire ∈ selection.val.explicitWires)) exact
    exact (List.perm_append_comm.trans (by
      simpa only [retainedAnchorWires, exact, selected] using split))
  exact (List.Perm.append_left (retainedAnchorWires input selection)
    (selectedExplicitFilter_perm input selection)).symm.trans partition

theorem retainedContext_append_explicit_perm
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    (retainedContext input selection inherited ++
      selection.val.explicitWires).Perm
      (inherited.extend selection.val.anchor) := by
  simpa only [retainedContext, Concrete.Elaboration.WireContext.extend,
    List.append_assoc] using
    List.Perm.append_left inherited
      (retainedAnchorWires_append_explicit_perm input selection)

/-- The local-wire equivalence that moves the explicit block out of the
anchor binder and into the selected factor. -/
noncomputable def anchorLocalEquiv
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    FiniteEquiv
      (Fin ((retainedAnchorWires input selection).length +
        selection.val.explicitWires.length))
      (Fin (Concrete.Elaboration.exactScopeWires input
        selection.val.anchor).length) :=
  let source := retainedAnchorWires input selection ++
    selection.val.explicitWires
  let target := Concrete.Elaboration.exactScopeWires input
    selection.val.anchor
  let permutation := retainedAnchorWires_append_explicit_perm input selection
  let targetNodup := Concrete.Elaboration.exactScopeWires_nodup input
    selection.val.anchor
  let sourceNodup := permutation.nodup_iff.mpr targetNodup
  (FiniteEquiv.finCast (by simp [source])).trans
    (IterationPartition.permIndexEquiv source target permutation sourceNodup
      targetNodup)

theorem anchorLocalEquiv_spec
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (index : Fin ((retainedAnchorWires input selection).length +
      selection.val.explicitWires.length)) :
    (Concrete.Elaboration.exactScopeWires input
      selection.val.anchor).get (anchorLocalEquiv input selection index) =
    (retainedAnchorWires input selection ++
      selection.val.explicitWires).get (Fin.cast (by simp) index) := by
  let source := retainedAnchorWires input selection ++
    selection.val.explicitWires
  let target := Concrete.Elaboration.exactScopeWires input
    selection.val.anchor
  let permutation := retainedAnchorWires_append_explicit_perm input selection
  let targetNodup := Concrete.Elaboration.exactScopeWires_nodup input
    selection.val.anchor
  let sourceNodup := permutation.nodup_iff.mpr targetNodup
  exact IterationPartition.permIndexEquiv_spec source target permutation
    sourceNodup targetNodup (Fin.cast (by simp [source]) index)

/-- Complete wire equivalence at the anchor, factored as identity on inherited
wires and the retained/explicit local partition. -/
noncomputable def anchorWireEquiv
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    FiniteEquiv
      (Fin (inherited.length +
        ((retainedAnchorWires input selection).length +
          selection.val.explicitWires.length)))
      (Fin (inherited.length +
        (Concrete.Elaboration.exactScopeWires input
          selection.val.anchor).length)) :=
  extendWireEquiv (FiniteEquiv.refl (Fin inherited.length))
    (anchorLocalEquiv input selection)

theorem retainedContext_member_full
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input)
    {wire : Fin input.wireCount}
    (member : wire ∈ retainedContext input selection inherited) :
    wire ∈ inherited.extend selection.val.anchor := by
  rcases List.mem_append.mp member with inheritedMember | retainedMember
  · exact List.mem_append.mpr (Or.inl inheritedMember)
  · exact List.mem_append.mpr (Or.inr
      ((Concrete.Elaboration.mem_exactScopeWires input
        selection.val.anchor wire).2
        ((mem_retainedAnchorWires input selection wire).1 retainedMember).1))

/-- Canonical inclusion of the retained wire context into the compiler's full
anchor context.  This is an index lookup into the authoritative context, not
a second compilation or context authority. -/
noncomputable def retainedContextIndexMap
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    Fin (retainedContext input selection inherited).length →
      Fin (inherited.extend selection.val.anchor).length :=
  fun index => Classical.choose (indexOf?_complete
    (retainedContext_member_full input selection inherited
      (List.get_mem _ index)))

theorem retainedContextIndexMap_spec
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input)
    (index : Fin (retainedContext input selection inherited).length) :
    (inherited.extend selection.val.anchor).get
        (retainedContextIndexMap input selection inherited index) =
      (retainedContext input selection inherited).get index := by
  unfold retainedContextIndexMap
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (retainedContext_member_full input selection inherited
      (List.get_mem _ index))))

/-- A checked selection never contains its own anchor in a selected child
subtree. -/
theorem anchor_not_selected
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val) :
    ¬ selection.val.SelectsRegion selection.val.anchor := by
  rintro ⟨root, rootMember, rootEncloses⟩
  exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
    input.property
    (selection.property.childRoots_direct root rootMember) rootEncloses

theorem keptNode_not_direct
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    {node : Fin input.nodeCount}
    (member : Concrete.Elaboration.LocalOccurrence.node node ∈
      keptOccurrences input selection) :
    node ∉ selection.val.directNodes := by
  rw [keptOccurrences, List.mem_filter] at member
  simpa [occurrenceSelected] using member.2

theorem keptChild_not_root
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    {child : Fin input.regionCount}
    (member : Concrete.Elaboration.LocalOccurrence.child child ∈
      keptOccurrences input selection) :
    child ∉ selection.val.childRoots := by
  rw [keptOccurrences, List.mem_filter] at member
  simpa [occurrenceSelected] using member.2

/-- Direct retained nodes cannot be incident to an explicit selection-owned
anchor wire. -/
theorem keptNode_noExplicitEndpoint
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {node : Fin input.val.nodeCount}
    (kept : Concrete.Elaboration.LocalOccurrence.node node ∈
      keptOccurrences input.val selection)
    {wire : Fin input.val.wireCount}
    (explicit : wire ∈ selection.val.explicitWires)
    (port : CPort) :
    ¬ input.val.EndpointOccurs wire ⟨node, port⟩ := by
  intro occurs
  have selectedNode : selection.val.SelectsNode node :=
    (selection.mem_selectedNodes node).1
      (selection.explicitWire_endpoint_selected explicit occurs)
  rcases selectedNode with direct | selectedRegion
  · exact keptNode_not_direct input.val selection kept direct
  · have nodeAtAnchor := (Concrete.Elaboration.mem_localOccurrences_node input.val
      selection.val.anchor node).1
      ((List.mem_filter.mp kept).1)
    rw [nodeAtAnchor] at selectedRegion
    exact anchor_not_selected input selection selectedRegion

/-- Every node below a retained direct child is outside the selection.  This
is the tree separation fact used by the restricted recursive compiler. -/
theorem keptChild_descendant_not_selectedNode
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {child : Fin input.val.regionCount}
    (kept : Concrete.Elaboration.LocalOccurrence.child child ∈
      keptOccurrences input.val selection)
    {node : Fin input.val.nodeCount}
    (below : input.val.Encloses child (input.val.nodes node).region) :
    ¬ selection.val.SelectsNode node := by
  intro selectedNode
  have childParent : (input.val.regions child).parent? =
      some selection.val.anchor :=
    (Concrete.Elaboration.mem_localOccurrences_child input.val
      selection.val.anchor child).1 ((List.mem_filter.mp kept).1)
  rcases selectedNode with direct | selectedRegion
  · have nodeAtAnchor := selection.property.directNodes_at_anchor node direct
    rw [nodeAtAnchor] at below
    exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
      input.property childParent below
  · obtain ⟨root, rootMember, rootBelow⟩ := selectedRegion
    have rootParent := selection.property.childRoots_direct root rootMember
    have equal :=
      Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
        input.property rootParent childParent rootBelow below
    exact keptChild_not_root input.val selection kept (equal ▸ rootMember)

/-- No occurrence recursively compiled below a retained child can mention an
explicit anchor wire. -/
theorem keptChild_descendant_noExplicitEndpoint
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {child : Fin input.val.regionCount}
    (kept : Concrete.Elaboration.LocalOccurrence.child child ∈
      keptOccurrences input.val selection)
    {node : Fin input.val.nodeCount}
    (below : input.val.Encloses child (input.val.nodes node).region)
    {wire : Fin input.val.wireCount}
    (explicit : wire ∈ selection.val.explicitWires)
    (port : CPort) :
    ¬ input.val.EndpointOccurs wire ⟨node, port⟩ := by
  intro occurs
  apply keptChild_descendant_not_selectedNode input selection kept below
  exact (selection.mem_selectedNodes node).1
    (selection.explicitWire_endpoint_selected explicit occurs)

end VisualProof.Refinement.Implementation.IterationSourceFactor
