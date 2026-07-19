import VisualProof.Rule.Soundness.Comprehension.InstantiationDrop

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationDrop

variable {signature : List Nat}
variable {origin : CheckedDiagram signature}
variable {p q : Nat}

@[simp] theorem raw_regions
    (state : InstantiationState origin p q)
    (region : Fin state.diagram.val.regionCount) :
    (dropInstantiationAtomsRaw state).regions region =
      state.diagram.val.regions region := rfl

@[simp] theorem raw_root
    (state : InstantiationState origin p q) :
    (dropInstantiationAtomsRaw state).root = state.diagram.val.root := rfl

@[simp] theorem raw_wire_scope
    (state : InstantiationState origin p q)
    (wire : Fin state.diagram.val.wireCount) :
    ((dropInstantiationAtomsRaw state).wires wire).scope =
      (state.diagram.val.wires wire).scope := rfl

@[simp] theorem raw_node
    (state : InstantiationState origin p q)
    (node : Fin (dropInstantiationAtomsRaw state).nodeCount) :
    (dropInstantiationAtomsRaw state).nodes node =
      state.diagram.val.nodes ((instantiationAtomDomain state).origin node) := rfl

@[simp] theorem raw_climb
    (state : InstantiationState origin p q)
    (steps : Nat) (region : Fin state.diagram.val.regionCount) :
    (dropInstantiationAtomsRaw state).climb steps region =
      state.diagram.val.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      cases hregion : state.diagram.val.regions region with
      | sheet =>
          simp only [ConcreteDiagram.climb, raw_regions, hregion]
          rfl
      | cut parent =>
          simpa [ConcreteDiagram.climb, raw_regions, hregion] using ih parent
      | bubble parent arity =>
          simpa [ConcreteDiagram.climb, raw_regions, hregion] using ih parent

theorem raw_encloses_iff
    (state : InstantiationState origin p q)
    (ancestor descendant : Fin state.diagram.val.regionCount) :
    (dropInstantiationAtomsRaw state).Encloses ancestor descendant ↔
      state.diagram.val.Encloses ancestor descendant := by
  simp only [ConcreteDiagram.Encloses, raw_climb]
  constructor <;> intro h <;> exact h

@[simp] theorem raw_wire_endpoints
    (state : InstantiationState origin p q)
    (wire : Fin state.diagram.val.wireCount) :
    ((dropInstantiationAtomsRaw state).wires wire).endpoints =
      (state.diagram.val.wires wire).endpoints.filterMap
        (instantiationAtomDomain state).reindexEndpoint? := rfl

theorem mem_raw_wire_endpoints_iff
    (state : InstantiationState origin p q)
    (wire : Fin state.diagram.val.wireCount)
    (endpoint : CEndpoint (dropInstantiationAtomsRaw state).nodeCount) :
    endpoint ∈ ((dropInstantiationAtomsRaw state).wires wire).endpoints ↔
      ∃ original,
        original ∈ (state.diagram.val.wires wire).endpoints ∧
          (instantiationAtomDomain state).reindexEndpoint? original =
            some endpoint := by
  rw [raw_wire_endpoints]
  exact List.mem_filterMap

theorem reindexEndpoint_origin
    (state : InstantiationState origin p q)
    {original : CEndpoint state.diagram.val.nodeCount}
    {mapped : CEndpoint (dropInstantiationAtomsRaw state).nodeCount}
    (hreindex : (instantiationAtomDomain state).reindexEndpoint? original =
      some mapped) :
    original = {
      node := (instantiationAtomDomain state).origin mapped.node
      port := mapped.port
    } := by
  obtain ⟨node, hnode, heq⟩ :=
    ((instantiationAtomDomain state).reindexEndpoint?_eq_some_iff
      original mapped).1 hreindex
  have horigin :=
    ((instantiationAtomDomain state).index?_eq_some_iff original.node node).1
      hnode
  subst mapped
  simp only at horigin
  cases original
  cases horigin
  rfl

theorem reindexEndpoint_some_injective
    (state : InstantiationState origin p q)
    {first second : CEndpoint state.diagram.val.nodeCount}
    {mapped : CEndpoint (dropInstantiationAtomsRaw state).nodeCount}
    (hfirst : (instantiationAtomDomain state).reindexEndpoint? first =
      some mapped)
    (hsecond : (instantiationAtomDomain state).reindexEndpoint? second =
      some mapped) :
    first = second := by
  rw [reindexEndpoint_origin state hfirst,
    reindexEndpoint_origin state hsecond]

private theorem filterMap_nodup_of_some_injective
    {values : List α} {f : α → Option β}
    (hnodup : values.Nodup)
    (hinjective : ∀ {first second mapped},
      f first = some mapped → f second = some mapped → first = second) :
    (values.filterMap f).Nodup := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.nodup_cons] at hnodup
      rcases hnodup with ⟨hhead, htail⟩
      cases hmapped : f head with
      | none => simpa [List.filterMap, hmapped] using ih htail
      | some mapped =>
          rw [show (head :: tail).filterMap f =
              mapped :: tail.filterMap f by simp [List.filterMap, hmapped],
            List.nodup_cons]
          constructor
          · intro hmember
            obtain ⟨other, hother, hotherMapped⟩ :=
              List.mem_filterMap.mp hmember
            exact hhead (by
              rw [hinjective hmapped hotherMapped]
              exact hother)
          · exact ih htail

theorem requiresPort_iff
    (state : InstantiationState origin p q)
    (node : Fin (dropInstantiationAtomsRaw state).nodeCount)
    (port : CPort) :
    (dropInstantiationAtomsRaw state).RequiresPort node port ↔
      state.diagram.val.RequiresPort
        ((instantiationAtomDomain state).origin node) port := by
  unfold ConcreteDiagram.RequiresPort
  rw [raw_node]
  cases hnode : state.diagram.val.nodes
      ((instantiationAtomDomain state).origin node) with
  | term => rfl
  | atom region binder =>
      simp only [raw_regions]
      cases state.diagram.val.regions binder <;> rfl
  | named => rfl

theorem endpointOccurs_of_surviving
    (state : InstantiationState origin p q)
    {wire : Fin state.diagram.val.wireCount}
    {endpoint : CEndpoint state.diagram.val.nodeCount}
    (hendpoint : state.diagram.val.EndpointOccurs wire endpoint)
    (hnode : (instantiationAtomDomain state).survives endpoint.node = true) :
    (dropInstantiationAtomsRaw state).EndpointOccurs wire {
      node := (instantiationAtomDomain state).index endpoint.node hnode
      port := endpoint.port
    } := by
  apply (mem_raw_wire_endpoints_iff state wire _).2
  refine ⟨endpoint, hendpoint, ?_⟩
  unfold SurvivorDomain.reindexEndpoint?
  rw [(instantiationAtomDomain state).index?_index endpoint.node hnode]
  rfl

theorem raw_wellFormed
    (state : InstantiationState origin p q) :
    (dropInstantiationAtomsRaw state).WellFormed signature where
  root_is_sheet := by
    simpa [ConcreteDiagram.RootIsSheet] using
      state.diagram.property.root_is_sheet
  only_root_is_sheet := by
    intro region hsheet
    exact state.diagram.property.only_root_is_sheet region (by simpa using hsheet)
  all_regions_reach_root := by
    intro region
    exact (raw_encloses_iff state _ _).2
      (state.diagram.property.all_regions_reach_root region)
  atom_binders_are_bubbles := by
    intro node
    rw [raw_node]
    cases hnode : state.diagram.val.nodes
        ((instantiationAtomDomain state).origin node) with
    | term => trivial
    | named => trivial
    | atom region binder =>
        have source := state.diagram.property.atom_binders_are_bubbles
          ((instantiationAtomDomain state).origin node)
        simp only [hnode] at source
        simpa only [raw_regions] using source
  atom_binders_enclose := by
    intro node
    rw [raw_node]
    cases hnode : state.diagram.val.nodes
        ((instantiationAtomDomain state).origin node) with
    | term => trivial
    | named => trivial
    | atom region binder =>
        have source := state.diagram.property.atom_binders_enclose
          ((instantiationAtomDomain state).origin node)
        simp only [hnode] at source
        exact (raw_encloses_iff state binder region).2 source
  named_references_resolve := by
    intro node
    rw [raw_node]
    cases hnode : state.diagram.val.nodes
        ((instantiationAtomDomain state).origin node) with
    | term => trivial
    | atom => trivial
    | named region definition arity =>
        have source := state.diagram.property.named_references_resolve
          ((instantiationAtomDomain state).origin node)
        simpa only [hnode] using source
  endpoints_are_valid := by
    intro wire endpoint hendpoint
    obtain ⟨original, horiginal, hreindex⟩ :=
      (mem_raw_wire_endpoints_iff state wire endpoint).1 hendpoint
    have hvalid := state.diagram.property.endpoints_are_valid wire original
      horiginal
    rw [reindexEndpoint_origin state hreindex] at hvalid
    exact (requiresPort_iff state endpoint.node endpoint.port).2 hvalid
  endpoints_are_nodup := by
    intro wire
    rw [raw_wire_endpoints]
    exact filterMap_nodup_of_some_injective
      (state.diagram.property.endpoints_are_nodup wire)
      (fun hfirst hsecond =>
        reindexEndpoint_some_injective state hfirst hsecond)
  wire_endpoints_are_disjoint := by
    intro first second hne endpoint hfirst
    rw [Bool.not_eq_true', decide_eq_false_iff_not]
    intro hsecond
    obtain ⟨firstOriginal, hfirstMember, hfirstMapped⟩ :=
      (mem_raw_wire_endpoints_iff state first endpoint).1 hfirst
    obtain ⟨secondOriginal, hsecondMember, hsecondMapped⟩ :=
      (mem_raw_wire_endpoints_iff state second endpoint).1 hsecond
    have hsame := reindexEndpoint_some_injective state hfirstMapped
      hsecondMapped
    subst secondOriginal
    have hdisjoint := state.diagram.property.wire_endpoints_are_disjoint
      first second hne firstOriginal hfirstMember
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at hdisjoint
    exact hdisjoint hsecondMember
  required_ports_are_covered := by
    intro node
    let original := (instantiationAtomDomain state).origin node
    have hsurvives := (instantiationAtomDomain state).origin_survives node
    have hindex : (instantiationAtomDomain state).index original hsurvives = node :=
      (instantiationAtomDomain state).index_origin node
    cases hnode : state.diagram.val.nodes original with
    | term region freePorts term =>
        have hcovered := state.diagram.property.required_ports_are_covered
          original
        simp only [hnode] at hcovered
        rw [raw_node, hnode]
        constructor
        · obtain ⟨wire, hwire⟩ := hcovered.1
          exact ⟨wire, hindex ▸ endpointOccurs_of_surviving state hwire hsurvives⟩
        · intro port
          obtain ⟨wire, hwire⟩ := hcovered.2 port
          exact ⟨wire, hindex ▸ endpointOccurs_of_surviving state hwire hsurvives⟩
    | atom region binder =>
        have hcovered := state.diagram.property.required_ports_are_covered
          original
        simp only [hnode] at hcovered
        rw [raw_node, hnode]
        cases hbinder : state.diagram.val.regions binder with
        | sheet => simp [hbinder]
        | cut parent => simp [hbinder]
        | bubble parent arity =>
            simp only [hbinder] at hcovered
            simp only [raw_regions, hbinder]
            intro port
            obtain ⟨wire, hwire⟩ := hcovered port
            exact ⟨wire, hindex ▸ endpointOccurs_of_surviving state hwire hsurvives⟩
    | named region definition arity =>
        have hcovered := state.diagram.property.required_ports_are_covered
          original
        simp only [hnode] at hcovered
        rw [raw_node, hnode]
        intro port
        obtain ⟨wire, hwire⟩ := hcovered port
        exact ⟨wire, hindex ▸ endpointOccurs_of_surviving state hwire hsurvives⟩
  wire_scopes_enclose := by
    intro wire endpoint hendpoint
    obtain ⟨original, horiginal, hreindex⟩ :=
      (mem_raw_wire_endpoints_iff state wire endpoint).1 hendpoint
    have hsource := state.diagram.property.wire_scopes_enclose wire original
      horiginal
    rw [reindexEndpoint_origin state hreindex] at hsource
    simpa only [raw_wire_scope, raw_node] using
      (raw_encloses_iff state _ _).2 hsource

/-- The executor's atom compaction is itself a checked diagram; the final
vacuous-binder step therefore composes with the existing certified modal
simulation instead of relying on an unchecked intermediate. -/
def checkedDrop (state : InstantiationState origin p q) :
    CheckedDiagram signature :=
  ⟨dropInstantiationAtomsRaw state, raw_wellFormed state⟩

end InstantiationDrop

end VisualProof.Rule
