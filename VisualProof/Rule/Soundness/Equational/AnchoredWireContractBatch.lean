import VisualProof.Rule.Soundness.Equational.AnchoredWireContractOrderedOpen

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- Moving a list headed by `endpoint` is exactly one primitive move followed
by the remaining simultaneous batch. -/
theorem moveEndpointsRaw_cons
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (tail : List (CEndpoint input.nodeCount))
    (distinct : sourceWire ≠ targetWire)
    (headNotTail : endpoint ∉ tail) :
    moveEndpointsRaw
        (moveEndpointRaw input sourceWire targetWire endpoint)
        sourceWire targetWire tail =
      moveEndpointsRaw input sourceWire targetWire (endpoint :: tail) := by
  cases input with
  | mk regionCount nodeCount wireCount root regions nodes wires =>
      change Fin wireCount at sourceWire targetWire
      change CEndpoint nodeCount at endpoint
      change List (CEndpoint nodeCount) at tail
      simp only [moveEndpointRaw, moveEndpointsRaw]
      congr 1
      funext candidate
      by_cases sourceEq : candidate = sourceWire
      · subst candidate
        simp only [if_pos]
        congr 1
        rw [List.filter_filter]
        apply congrArg (fun predicate =>
          List.filter predicate (wires sourceWire).endpoints)
        funext current
        by_cases same : current = endpoint <;>
          by_cases member : current ∈ tail <;>
            simp [same, member] <;> assumption
      · by_cases targetEq : candidate = targetWire
        · subst candidate
          simp only [if_pos, distinct.symm]
          simp only [if_false]
          cases targetValue : wires targetWire with
          | mk scope existing =>
              congr 1
              exact List.append_assoc existing [endpoint] tail
        · simp only [sourceEq, targetEq, if_false]

theorem moveEndpointsRaw_selected_occurs_target
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount))
    (distinct : sourceWire ≠ targetWire)
    {endpoint : CEndpoint input.nodeCount}
    (member : endpoint ∈ endpoints) :
    (moveEndpointsRaw input sourceWire targetWire endpoints).EndpointOccurs
      targetWire endpoint := by
  unfold ConcreteDiagram.EndpointOccurs moveEndpointsRaw
  simp only [if_neg distinct.symm, if_pos]
  exact List.mem_append_right _ member

theorem moveEndpointsRaw_selected_not_occurs_source
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount))
    {endpoint : CEndpoint input.nodeCount}
    (member : endpoint ∈ endpoints) :
    ¬ (moveEndpointsRaw input sourceWire targetWire endpoints).EndpointOccurs
      sourceWire endpoint := by
  unfold ConcreteDiagram.EndpointOccurs moveEndpointsRaw
  simp only [if_pos]
  intro kept
  exact (of_decide_eq_true (List.mem_filter.mp kept).2) member

theorem moveEndpointsRaw_selected_occurs_iff
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount))
    (distinct : sourceWire ≠ targetWire)
    {endpoint : CEndpoint input.nodeCount}
    (member : endpoint ∈ endpoints)
    (sourceOccurs : input.EndpointOccurs sourceWire endpoint)
    (disjoint : input.WireEndpointsAreDisjoint)
    (candidate : Fin input.wireCount) :
    (moveEndpointsRaw input sourceWire targetWire endpoints).EndpointOccurs
        candidate endpoint ↔ candidate = targetWire := by
  by_cases sourceEq : candidate = sourceWire
  · subst candidate
    constructor
    · exact fun occurs => False.elim
        (moveEndpointsRaw_selected_not_occurs_source input sourceWire targetWire
          endpoints member occurs)
    · exact fun equality => False.elim (distinct equality)
  · by_cases targetEq : candidate = targetWire
    · subst candidate
      constructor
      · intro _
        rfl
      · intro _
        exact moveEndpointsRaw_selected_occurs_target input sourceWire
          targetWire endpoints distinct member
    · have candidateAbsent : ¬ input.EndpointOccurs candidate endpoint := by
        intro candidateOccurs
        have ownerEq := ConcreteElaboration.endpoint_wire_unique disjoint
          sourceOccurs candidateOccurs
        exact sourceEq ownerEq.symm
      unfold ConcreteDiagram.EndpointOccurs moveEndpointsRaw
      simp only [if_neg sourceEq, if_neg targetEq]
      constructor
      · exact fun occurs => False.elim (candidateAbsent occurs)
      · exact fun equality => False.elim (targetEq equality)

theorem moveEndpointsRaw_other_occurs_iff
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount))
    (current : CEndpoint input.nodeCount)
    (notSelected : current ∉ endpoints)
    (candidate : Fin input.wireCount) :
    (moveEndpointsRaw input sourceWire targetWire endpoints).EndpointOccurs
        candidate current ↔ input.EndpointOccurs candidate current := by
  unfold ConcreteDiagram.EndpointOccurs moveEndpointsRaw
  by_cases sourceEq : candidate = sourceWire
  · subst candidate
    simp only [if_pos, List.mem_filter]
    exact and_iff_left (decide_eq_true notSelected)
  · by_cases targetEq : candidate = targetWire
    · subst candidate
      simp only [if_neg sourceEq, if_pos, List.mem_append]
      exact or_iff_left notSelected
    · simp only [if_neg sourceEq, if_neg targetEq]

theorem moveEndpointsRaw_covered
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount))
    (distinct : sourceWire ≠ targetWire)
    (current : CEndpoint input.nodeCount)
    (covered : ∃ wire, input.EndpointOccurs wire current) :
    ∃ wire, (moveEndpointsRaw input sourceWire targetWire endpoints
      ).EndpointOccurs wire current := by
  by_cases selected : current ∈ endpoints
  · exact ⟨targetWire, moveEndpointsRaw_selected_occurs_target input
      sourceWire targetWire endpoints distinct selected⟩
  · obtain ⟨wire, occurs⟩ := covered
    exact ⟨wire, (moveEndpointsRaw_other_occurs_iff input sourceWire
      targetWire endpoints current selected wire).mpr occurs⟩

/-- Simultaneously moving a noduplicated source subset to an enclosing target
wire preserves the full checked-diagram contract. -/
theorem moveEndpointsRaw_wellFormed
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoints : List (CEndpoint input.nodeCount))
    (distinct : sourceWire ≠ targetWire)
    (nodup : endpoints.Nodup)
    (sourceOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.EndpointOccurs sourceWire endpoint)
    (targetEncloses : ∀ endpoint, endpoint ∈ endpoints →
      input.Encloses (input.wires targetWire).scope
        (input.nodes endpoint.node).region) :
    (moveEndpointsRaw input sourceWire targetWire endpoints).WellFormed
      signature := by
  refine {
    root_is_sheet := by simpa [ConcreteDiagram.RootIsSheet] using
      wellFormed.root_is_sheet
    only_root_is_sheet := by
      intro region sheet
      apply wellFormed.only_root_is_sheet region
      simpa using sheet
    all_regions_reach_root := by
      intro region
      rcases wellFormed.all_regions_reach_root region with ⟨steps, reached⟩
      exact ⟨steps, by simpa [moveEndpointsRaw_climb] using reached⟩
    atom_binders_are_bubbles := by
      intro node
      change Fin input.nodeCount at node
      cases shape : input.nodes node with
      | term region arity term => simp [moveEndpointsRaw, shape]
      | named region definition arity => simp [moveEndpointsRaw, shape]
      | atom region binder =>
          have original := wellFormed.atom_binders_are_bubbles node
          rw [shape] at original
          simpa [moveEndpointsRaw, shape] using original
    atom_binders_enclose := by
      intro node
      change Fin input.nodeCount at node
      cases shape : input.nodes node with
      | term region arity term => simp [moveEndpointsRaw, shape]
      | named region definition arity => simp [moveEndpointsRaw, shape]
      | atom region binder =>
          have original := wellFormed.atom_binders_enclose node
          rw [shape] at original
          simp only [moveEndpointsRaw, shape]
          exact (moveEndpointsRaw_encloses_iff input sourceWire targetWire
            endpoints binder region).mpr original
    named_references_resolve := by
      intro node
      change Fin input.nodeCount at node
      cases shape : input.nodes node with
      | term region arity term => simp [moveEndpointsRaw, shape]
      | atom region binder => simp [moveEndpointsRaw, shape]
      | named region definition arity =>
          have original := wellFormed.named_references_resolve node
          rw [shape] at original
          simpa [moveEndpointsRaw, shape] using original
    endpoints_are_valid := by
      intro wire current occurs
      change Fin input.wireCount at wire
      change CEndpoint input.nodeCount at current
      have targetValid : (moveEndpointsRaw input sourceWire targetWire endpoints
          ).RequiresPort current.node current.port ↔
          input.RequiresPort current.node current.port := by
        unfold ConcreteDiagram.RequiresPort
        cases shape : input.nodes current.node with
        | term region arity term => simp [moveEndpointsRaw, shape]
        | named region definition arity => simp [moveEndpointsRaw, shape]
        | atom region binder =>
            cases binderShape : input.regions binder <;>
              simp [moveEndpointsRaw, shape, binderShape]
      rw [targetValid]
      by_cases selected : current ∈ endpoints
      · exact wellFormed.endpoints_are_valid sourceWire current
          (sourceOccurs current selected)
      · exact wellFormed.endpoints_are_valid wire current
          ((moveEndpointsRaw_other_occurs_iff input sourceWire targetWire
            endpoints current selected wire).mp occurs)
    endpoints_are_nodup := by
      intro wire
      change Fin input.wireCount at wire
      by_cases sourceEq : wire = sourceWire
      · subst wire
        simpa [moveEndpointsRaw] using
          (wellFormed.endpoints_are_nodup sourceWire).filter
            (fun current => decide (current ∉ endpoints))
      · by_cases targetEq : wire = targetWire
        · subst wire
          have disjointLists : ∀ current ∈ (input.wires targetWire).endpoints,
              ∀ selected ∈ endpoints, current ≠ selected := by
            intro current currentMem selected selectedMem equality
            subst current
            have ownerEq := ConcreteElaboration.endpoint_wire_unique
              wellFormed.wire_endpoints_are_disjoint
              (sourceOccurs selected selectedMem)
              (show input.EndpointOccurs targetWire selected from currentMem)
            exact distinct ownerEq
          change ((if targetWire = sourceWire then
              { scope := (input.wires targetWire).scope
                endpoints := (input.wires targetWire).endpoints.filter
                  fun current => decide (current ∉ endpoints) }
            else if targetWire = targetWire then
              { scope := (input.wires targetWire).scope
                endpoints := (input.wires targetWire).endpoints ++ endpoints }
            else input.wires targetWire).endpoints).Nodup
          split
          · rename_i same
            exact False.elim (sourceEq same)
          · simp only [if_pos]
            exact List.nodup_append.mpr
              ⟨wellFormed.endpoints_are_nodup targetWire, nodup, disjointLists⟩
        · simp [moveEndpointsRaw, sourceEq, targetEq,
            wellFormed.endpoints_are_nodup wire]
    wire_endpoints_are_disjoint := by
      unfold ConcreteDiagram.WireEndpointsAreDisjoint
      simp only [bne_iff_ne]
      intro first second different current firstOccurs
      change Fin input.wireCount at first second
      change CEndpoint input.nodeCount at current
      rw [Bool.not_eq_true']
      apply decide_eq_false
      intro secondOccurs
      by_cases selected : current ∈ endpoints
      · have selectedIff := moveEndpointsRaw_selected_occurs_iff input
          sourceWire targetWire endpoints distinct selected
          (sourceOccurs current selected) wellFormed.wire_endpoints_are_disjoint
        have firstTarget := (selectedIff first).mp firstOccurs
        have secondTarget := (selectedIff second).mp secondOccurs
        exact different (firstTarget.trans secondTarget.symm)
      · have originalNot := wellFormed.wire_endpoints_are_disjoint first
          second (by simpa only [bne_iff_ne] using different) current
          ((moveEndpointsRaw_other_occurs_iff input sourceWire targetWire
            endpoints current selected first).mp firstOccurs)
        rw [Bool.not_eq_true'] at originalNot
        exact (of_decide_eq_false originalNot)
          ((moveEndpointsRaw_other_occurs_iff input sourceWire targetWire
            endpoints current selected second).mp secondOccurs)
    required_ports_are_covered := by
      intro node
      change Fin input.nodeCount at node
      have cover := wellFormed.required_ports_are_covered node
      cases shape : input.nodes node with
      | term region freePorts term =>
          rw [shape] at cover
          simp only [moveEndpointsRaw, shape]
          exact ⟨moveEndpointsRaw_covered input sourceWire targetWire endpoints
              distinct ⟨node, .output⟩ cover.1,
            fun index => moveEndpointsRaw_covered input sourceWire targetWire
              endpoints distinct ⟨node, .free index⟩ (cover.2 index)⟩
      | named region definition arity =>
          rw [shape] at cover
          simp only [moveEndpointsRaw, shape]
          exact fun index => moveEndpointsRaw_covered input sourceWire targetWire
            endpoints distinct ⟨node, .arg index⟩ (cover index)
      | atom region binder =>
          rw [shape] at cover
          cases binderShape : input.regions binder with
          | sheet => simp [moveEndpointsRaw, shape, binderShape]
          | cut parent => simp [moveEndpointsRaw, shape, binderShape]
          | bubble parent arity =>
              simp only [binderShape] at cover
              simp only [moveEndpointsRaw, shape, binderShape]
              exact fun index => moveEndpointsRaw_covered input sourceWire
                targetWire endpoints distinct ⟨node, .arg index⟩ (cover index)
    wire_scopes_enclose := by
      intro wire current occurs
      change Fin input.wireCount at wire
      change CEndpoint input.nodeCount at current
      by_cases selected : current ∈ endpoints
      · have wireEq := (moveEndpointsRaw_selected_occurs_iff input sourceWire
          targetWire endpoints distinct selected (sourceOccurs current selected)
          wellFormed.wire_endpoints_are_disjoint wire).mp occurs
        subst wire
        simpa only [moveEndpointsRaw_wire_scope, moveEndpointsRaw_nodes] using
          (moveEndpointsRaw_encloses_iff input sourceWire targetWire endpoints
            (input.wires targetWire).scope
            (input.nodes current.node).region).mpr
              (targetEncloses current selected)
      · have originalOccurs := (moveEndpointsRaw_other_occurs_iff input
            sourceWire targetWire endpoints current selected wire).mp occurs
        have original := wellFormed.wire_scopes_enclose wire current originalOccurs
        simpa only [moveEndpointsRaw_wire_scope, moveEndpointsRaw_nodes] using
          (moveEndpointsRaw_encloses_iff input sourceWire targetWire endpoints
            (input.wires wire).scope (input.nodes current.node).region).mpr
              original
  }

end AnchoredWireContractSoundness

end VisualProof.Rule
