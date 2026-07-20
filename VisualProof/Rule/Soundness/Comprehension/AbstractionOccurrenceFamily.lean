import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedPartition
import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedKept

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- A boundary wire of one certified occurrence cannot be internal to any
other certified occurrence.  This is the semantic independence property
behind simultaneous hidden-wire witnesses. -/
theorem touchingWire_not_internal
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (left right : Fin occurrences.length)
    (wire : Fin input.val.wireCount)
    (touching : wire ∈ (occurrences.get left).selection.touchingWires) :
    wire ∉ (occurrences.get right).selection.internalWires := by
  intro internal
  by_cases equal : left = right
  · subst right
    exact ((occurrences.get left).selection
      |>.mem_touchingWires_consequences touching).1 internal
  · obtain ⟨endpoint, endpointOccurs, leftSelected⟩ :=
      ((occurrences.get left).selection
        |>.mem_touchingWires_consequences touching).2
    have rightSelected : endpoint.node ∈
        (occurrences.get right).selection.selectedNodes := by
      rcases ((occurrences.get right).selection
          |>.mem_internalWires_expanded wire).1 internal with
        selectedScope | explicit
      · obtain ⟨root, rootMember, rootEnclosesScope⟩ := selectedScope
        have scopeEnclosesOwner := input.property.wire_scopes_enclose wire
          endpoint endpointOccurs
        exact ((occurrences.get right).selection.mem_selectedNodes
          endpoint.node).2 (Or.inr ⟨root, rootMember,
            ConcreteElaboration.checked_encloses_trans input.property
              rootEnclosesScope scopeEnclosesOwner⟩)
      · exact (occurrences.get right).selection.explicitWire_endpoint_selected
          explicit endpointOccurs
    exact payload.nodes_disjoint left right equal endpoint.node leftSelected
      rightSelected

/-- Every extracted fragment wire originates in exactly the internal-or-
touching closure of its certified host occurrence. -/
theorem occurrenceFragmentWire_origin_mem_closure
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (wire : Fin (occurrenceLayout input occurrence).wireCount) :
    input.val.fragmentWireOrigin occurrence.selection
          (occurrenceLayout input occurrence) wire ∈
        occurrence.selection.internalWires ∨
      input.val.fragmentWireOrigin occurrence.selection
          (occurrenceLayout input occurrence) wire ∈
        occurrence.selection.touchingWires := by
  refine Fin.addCases (m := occurrence.selection.internalWires.length)
    (n := occurrence.selection.touchingWires.length) (fun internal => ?_)
    (fun touching => ?_) wire
  · left
    have originEq : input.val.fragmentWireOrigin occurrence.selection
        (occurrenceLayout input occurrence)
          (Fin.castAdd occurrence.selection.touchingWires.length internal) =
        occurrence.selection.internalWires.get internal := by
      exact Fin.addCases_left internal
    exact originEq.symm ▸
      List.get_mem occurrence.selection.internalWires internal
  · right
    have originEq : input.val.fragmentWireOrigin occurrence.selection
        (occurrenceLayout input occurrence)
          (Fin.natAdd occurrence.selection.internalWires.length touching) =
        occurrence.selection.touchingWires.get touching := by
      exact Fin.addCases_right touching
    exact originEq.symm ▸
      List.get_mem occurrence.selection.touchingWires touching

/-- Filtering to actual survivors does not change a subsequent partial-map
compilation; it only makes the domain total for `survivorOccurrence`. -/
theorem survivingSources_filterMap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)) :
    (trace.survivingSources values).filterMap trace.survivingOccurrence? =
      values.filterMap trace.survivingOccurrence? := by
  unfold survivingSources
  induction values with
  | nil => rfl
  | cons head tail ih =>
      cases mapped : trace.survivingOccurrence? head with
      | none => simp [mapped, ih]
      | some target => simp [mapped, ih]

/-- The total survivor map on the filtered source partition is exactly the
authoritative target `filterMap`. -/
theorem survivingSources_map_survivor
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)) :
    (trace.survivingSources values).map trace.survivorOccurrence =
      values.filterMap trace.survivingOccurrence? := by
  rw [← trace.survivingSources_filterMap values]
  symm
  apply trace.filterMap_eq_map_survivor
  intro occurrence member
  have some := (mem_survivingSources trace values occurrence).1 member |>.2
  exact Option.isSome_iff_exists.mp some

/-- Assemble independently chosen occurrence valuations.  Disjoint internal
wire certificates make the selected valuation unique at every host wire. -/
noncomputable def occurrenceFamilyEnvironment
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (indices : List (Fin occurrences.length))
    (context : ConcreteElaboration.WireContext input.val)
    (values : ∀ index : Fin occurrences.length,
      Fin context.length → D)
    (fallback : Fin context.length → D) :
    Fin context.length → D := by
  classical
  exact fun hostIndex =>
    if represented : ∃ index, index ∈ indices ∧
        context.get hostIndex ∈
          (occurrences.get index).selection.internalWires
    then values (Classical.choose represented) hostIndex
    else fallback hostIndex

theorem occurrenceFamilyEnvironment_eq_member
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (indices : List (Fin occurrences.length))
    (context : ConcreteElaboration.WireContext input.val)
    (values : ∀ index : Fin occurrences.length,
      Fin context.length → D)
    (fallback : Fin context.length → D)
    (index : Fin occurrences.length)
    (indexMember : index ∈ indices)
    (hostIndex : Fin context.length)
    (internal : context.get hostIndex ∈
      (occurrences.get index).selection.internalWires) :
    occurrenceFamilyEnvironment input occurrences indices context values
        fallback hostIndex = values index hostIndex := by
  classical
  unfold occurrenceFamilyEnvironment
  rw [dif_pos ⟨index, indexMember, internal⟩]
  let chosen := Classical.choose
    (show ∃ candidate, candidate ∈ indices ∧
      context.get hostIndex ∈
        (occurrences.get candidate).selection.internalWires from
      ⟨index, indexMember, internal⟩)
  have chosenSpec := Classical.choose_spec
    (show ∃ candidate, candidate ∈ indices ∧
      context.get hostIndex ∈
        (occurrences.get candidate).selection.internalWires from
      ⟨index, indexMember, internal⟩)
  have chosenEq : chosen = index := by
    by_cases equal : chosen = index
    · exact equal
    · exact False.elim (payload.wires_disjoint chosen index equal
        (context.get hostIndex) chosenSpec.2 internal)
  change values chosen hostIndex = values index hostIndex
  rw [chosenEq]

theorem occurrenceFamilyEnvironment_eq_fallback
    (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (indices : List (Fin occurrences.length))
    (context : ConcreteElaboration.WireContext input.val)
    (values : ∀ index : Fin occurrences.length,
      Fin context.length → D)
    (fallback : Fin context.length → D)
    (hostIndex : Fin context.length)
    (outside : ∀ index, index ∈ indices →
      context.get hostIndex ∉
        (occurrences.get index).selection.internalWires) :
    occurrenceFamilyEnvironment input occurrences indices context values
        fallback hostIndex = fallback hostIndex := by
  classical
  unfold occurrenceFamilyEnvironment
  rw [dif_neg]
  rintro ⟨index, member, internal⟩
  exact outside index member internal

/-- On every wire represented by one occurrence fragment, the simultaneous
family valuation agrees with that occurrence's independently realized
valuation. -/
theorem occurrenceFamilyEnvironment_eq_value_on_closure
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (indices : List (Fin occurrences.length))
    (context : ConcreteElaboration.WireContext input.val)
    (values : ∀ index : Fin occurrences.length,
      Fin context.length → D)
    (fallback : Fin context.length → D)
    (preserves : ∀ index hostIndex,
      context.get hostIndex ∉
          (occurrences.get index).selection.internalWires →
        values index hostIndex = fallback hostIndex)
    (index : Fin occurrences.length)
    (indexMember : index ∈ indices)
    (hostIndex : Fin context.length)
    (represented : context.get hostIndex ∈
        (occurrences.get index).selection.internalWires ∨
      context.get hostIndex ∈
        (occurrences.get index).selection.touchingWires) :
    occurrenceFamilyEnvironment input occurrences indices context values
        fallback hostIndex = values index hostIndex := by
  rcases represented with internal | touching
  · exact occurrenceFamilyEnvironment_eq_member payload indices context values
      fallback index indexMember hostIndex internal
  · rw [occurrenceFamilyEnvironment_eq_fallback input occurrences indices
      context values fallback hostIndex]
    · symm
      exact preserves index hostIndex
        ((occurrences.get index).selection
          |>.mem_touchingWires_consequences touching).1
    · intro other otherMember
      exact touchingWire_not_internal payload index other
        (context.get hostIndex) touching

end AbstractionRawTrace

end VisualProof.Rule
