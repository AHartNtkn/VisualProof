import VisualProof.Rule.Soundness.Equational.AnchoredWireContract

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

@[simp] theorem moveEndpointRaw_requiresPort_iff
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (node : Fin input.nodeCount) (port : CPort) :
    (moveEndpointRaw input sourceWire targetWire endpoint).RequiresPort
        node port ↔
      input.RequiresPort node port := by
  unfold ConcreteDiagram.RequiresPort
  cases shape : input.nodes node with
  | term region arity term => simp [moveEndpointRaw, shape]
  | named region definition arity => simp [moveEndpointRaw, shape]
  | atom region binder =>
      cases binderShape : input.regions binder <;>
        simp [moveEndpointRaw, shape, binderShape]

/-- Moving one endpoint to a distinct wire whose scope encloses that endpoint
preserves the complete checked-diagram contract. -/
theorem moveEndpointRaw_wellFormed
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.EndpointOccurs sourceWire endpoint)
    (targetEncloses : input.Encloses (input.wires targetWire).scope
      (input.nodes endpoint.node).region) :
    (moveEndpointRaw input sourceWire targetWire endpoint).WellFormed
      signature := by
  have selectedIff : ∀ candidate,
      (moveEndpointRaw input sourceWire targetWire endpoint).EndpointOccurs
          candidate endpoint ↔ candidate = targetWire :=
    moveEndpointRaw_selected_occurs_iff input sourceWire targetWire endpoint
      distinct sourceOccurs wellFormed.wire_endpoints_are_disjoint
  refine {
    root_is_sheet := ?_
    only_root_is_sheet := ?_
    all_regions_reach_root := ?_
    atom_binders_are_bubbles := ?_
    atom_binders_enclose := ?_
    named_references_resolve := ?_
    endpoints_are_valid := ?_
    endpoints_are_nodup := ?_
    wire_endpoints_are_disjoint := ?_
    required_ports_are_covered := ?_
    wire_scopes_enclose := ?_
  }
  · simpa [ConcreteDiagram.RootIsSheet] using wellFormed.root_is_sheet
  · intro region sheet
    change Fin input.regionCount at region
    apply wellFormed.only_root_is_sheet region
    simpa using sheet
  · intro region
    change Fin input.regionCount at region
    rcases wellFormed.all_regions_reach_root region with ⟨steps, reached⟩
    exact ⟨steps, by simpa [moveEndpointRaw_climb] using reached⟩
  · intro node
    change Fin input.nodeCount at node
    cases shape : input.nodes node with
    | term region arity term => simp [moveEndpointRaw, shape]
    | named region definition arity => simp [moveEndpointRaw, shape]
    | atom region binder =>
        have original := wellFormed.atom_binders_are_bubbles node
        rw [shape] at original
        simpa [moveEndpointRaw, shape] using original
  · intro node
    change Fin input.nodeCount at node
    cases shape : input.nodes node with
    | term region arity term => simp [moveEndpointRaw, shape]
    | named region definition arity => simp [moveEndpointRaw, shape]
    | atom region binder =>
        have original := wellFormed.atom_binders_enclose node
        rw [shape] at original
        simp only [moveEndpointRaw, shape]
        exact (moveEndpointRaw_encloses_iff input sourceWire targetWire endpoint
          binder region).mpr original
  · intro node
    change Fin input.nodeCount at node
    cases shape : input.nodes node with
    | term region arity term => simp [moveEndpointRaw, shape]
    | atom region binder => simp [moveEndpointRaw, shape]
    | named region definition arity =>
        have original := wellFormed.named_references_resolve node
        rw [shape] at original
        simpa [moveEndpointRaw, shape] using original
  · intro wire current occurs
    change Fin input.wireCount at wire
    change CEndpoint input.nodeCount at current
    rw [moveEndpointRaw_requiresPort_iff]
    by_cases selected : current = endpoint
    · subst current
      exact wellFormed.endpoints_are_valid sourceWire endpoint sourceOccurs
    · exact wellFormed.endpoints_are_valid wire current
        ((moveEndpointRaw_other_occurs_iff input sourceWire targetWire endpoint
          current selected wire).mp occurs)
  · intro wire
    change Fin input.wireCount at wire
    by_cases sourceEq : wire = sourceWire
    · subst wire
      simpa [moveEndpointRaw] using
        (wellFormed.endpoints_are_nodup sourceWire).filter
          (fun current => decide (current ≠ endpoint))
    · by_cases targetEq : wire = targetWire
      · subst wire
        have endpointAbsent : endpoint ∉ (input.wires targetWire).endpoints := by
          intro targetOccurs
          exact distinct (ConcreteElaboration.endpoint_wire_unique
            wellFormed.wire_endpoints_are_disjoint sourceOccurs targetOccurs)
        change ((if targetWire = sourceWire then
            { scope := (input.wires targetWire).scope
              endpoints := (input.wires targetWire).endpoints.filter fun current =>
                decide (current ≠ endpoint) }
          else if targetWire = targetWire then
            { scope := (input.wires targetWire).scope
              endpoints := (input.wires targetWire).endpoints ++ [endpoint] }
          else input.wires targetWire).endpoints).Nodup
        split
        · rename_i same
          exact False.elim (sourceEq same)
        · simp only [if_pos]
          apply List.nodup_append.mpr
          refine ⟨wellFormed.endpoints_are_nodup targetWire, by simp, ?_⟩
          intro current currentMem selected selectedMem
          have selectedEq : selected = endpoint :=
            List.mem_singleton.mp selectedMem
          subst selected
          exact fun equality => endpointAbsent (equality ▸ currentMem)
      · change ((if wire = sourceWire then
            { scope := (input.wires wire).scope
              endpoints := (input.wires wire).endpoints.filter fun current =>
                decide (current ≠ endpoint) }
          else if wire = targetWire then
            { scope := (input.wires wire).scope
              endpoints := (input.wires wire).endpoints ++ [endpoint] }
          else input.wires wire).endpoints).Nodup
        simp only [sourceEq, targetEq, if_false]
        exact wellFormed.endpoints_are_nodup wire
  · unfold ConcreteDiagram.WireEndpointsAreDisjoint
    simp only [bne_iff_ne]
    intro first second different current firstOccurs
    change Fin input.wireCount at first second
    change CEndpoint input.nodeCount at current
    rw [Bool.not_eq_true']
    apply decide_eq_false
    intro secondOccurs
    by_cases selected : current = endpoint
    · subst current
      have firstEq := (selectedIff first).mp firstOccurs
      have secondEq := (selectedIff second).mp secondOccurs
      exact different (firstEq.trans secondEq.symm)
    · have originalNot := wellFormed.wire_endpoints_are_disjoint first second
        (by simpa only [bne_iff_ne] using different) current
        ((moveEndpointRaw_other_occurs_iff input sourceWire targetWire endpoint
          current selected first).mp firstOccurs)
      rw [Bool.not_eq_true'] at originalNot
      exact (of_decide_eq_false originalNot)
        ((moveEndpointRaw_other_occurs_iff input sourceWire targetWire endpoint
          current selected second).mp secondOccurs)
  · intro node
    change Fin input.nodeCount at node
    have cover := wellFormed.required_ports_are_covered node
    cases shape : input.nodes node with
    | term region freePorts term =>
        rw [shape] at cover
        simp only [moveEndpointRaw, shape]
        constructor
        · exact moveEndpointRaw_covered input sourceWire targetWire endpoint
            ⟨node, .output⟩ distinct cover.1
        · intro index
          exact moveEndpointRaw_covered input sourceWire targetWire endpoint
            ⟨node, .free index⟩ distinct (cover.2 index)
    | named region definition arity =>
        rw [shape] at cover
        simp only [moveEndpointRaw, shape]
        intro index
        exact moveEndpointRaw_covered input sourceWire targetWire endpoint
          ⟨node, .arg index⟩ distinct (cover index)
    | atom region binder =>
        rw [shape] at cover
        cases binderShape : input.regions binder with
        | sheet => simp [moveEndpointRaw, shape, binderShape]
        | cut parent => simp [moveEndpointRaw, shape, binderShape]
        | bubble parent arity =>
            simp only [binderShape] at cover
            simp only [moveEndpointRaw, shape, binderShape]
            intro index
            exact moveEndpointRaw_covered input sourceWire targetWire endpoint
              ⟨node, .arg index⟩ distinct (cover index)
  · intro wire current occurs
    change Fin input.wireCount at wire
    change CEndpoint input.nodeCount at current
    by_cases selected : current = endpoint
    · subst current
      have wireEq := (selectedIff wire).mp occurs
      subst wire
      simpa only [moveEndpointRaw_wire_scope, moveEndpointRaw_nodes] using
        (moveEndpointRaw_encloses_iff input sourceWire targetWire endpoint
          (input.wires targetWire).scope
          (input.nodes endpoint.node).region).mpr targetEncloses
    · have originalOccurs :=
        (moveEndpointRaw_other_occurs_iff input sourceWire targetWire endpoint
          current selected wire).mp occurs
      have original := wellFormed.wire_scopes_enclose wire current originalOccurs
      simpa only [moveEndpointRaw_wire_scope, moveEndpointRaw_nodes] using
        (moveEndpointRaw_encloses_iff input sourceWire targetWire endpoint
          (input.wires wire).scope (input.nodes current.node).region).mpr original

end AnchoredWireContractSoundness

end VisualProof.Rule
