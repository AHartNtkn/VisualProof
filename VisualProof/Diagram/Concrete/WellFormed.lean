import VisualProof.Diagram.Concrete.Core

namespace VisualProof

/-- Structured validation failures carry stable numeric IDs, not dependent data. -/
inductive WFError
  | rootNotSheet
  | secondSheet (region : Nat)
  | parentDoesNotReachRoot (region : Nat)
  | referenceSignatureMismatch (node : Nat)
  | invalidEndpoint (wire node : Nat) (port : CPort)
  | duplicateEndpoint (wire node : Nat) (port : CPort)
  | missingOrDuplicatePort (node : Nat) (port : CPort)
  | atomSignatureMismatch (node : Nat) (port : CPort)
  | refSignatureMismatch (node : Nat) (port : CPort)
  | identityArityTooSmall (node : Nat)
  | identitySignatureMismatch (node index : Nat)
  | wireScopeDoesNotEnclose (wire node : Nat) (port : CPort)
  deriving Repr, DecidableEq

namespace ConcreteDiagram

private def endpointCount (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId) (port : CPort) : Nat :=
  (diagram.endpointOccurrences.filter fun occurrence =>
    occurrence.2 == ⟨node, port⟩).length

/-- The stored root is a sheet. -/
def RootIsSheet (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.regions diagram.root = .sheet

/-- No region other than the root is a sheet. -/
def OnlyRootIsSheet (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.regionsList.all (fun region =>
    decide (diagram.regions region = .sheet → region = diagram.root)) = true

/-- Every bounded parent chain reaches the unique root. -/
def AllRegionsReachRoot (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.regionsList.all (fun region =>
    decide (diagram.Encloses diagram.root region)) = true

/-- Every ref carries exactly the chronological definition signature it names. -/
def ReferencesMatch (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) : Prop :=
  diagram.nodesList.all (fun node =>
    match diagram.nodes node with
    | .ref _ definition args => args == definitions.get definition
    | _ => true) = true

/-- Every stored endpoint names a constructor-derived port. -/
def PortsExist (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.endpointOccurrences.all (fun occurrence =>
    decide (occurrence.2.port ∈ diagram.requiredPorts occurrence.2.node)) = true

/-- One endpoint value cannot occur twice, on one wire or across wires. -/
def NoDuplicateEndpoints (diagram : ConcreteDiagram definitionCount) : Prop :=
  ((diagram.endpointOccurrences.map Prod.snd).eraseDups).length =
    diagram.endpointOccurrences.length

/-- Every derived node port has exactly one incident wire. -/
def PortsCoveredExactlyOnce (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.nodesList.all (fun node =>
    (diagram.requiredPorts node).all fun port =>
      diagram.endpointCount node port == 1 &&
        (diagram.endpointOwner? ⟨node, port⟩).isSome) = true

/-- Atom heads and positional arguments have their intrinsic signatures. -/
def AtomPortsTyped (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.nodesList.all (fun node =>
    match diagram.nodes node with
    | .atom _ args =>
        (match diagram.endpointOwner? ⟨node, .head⟩ with
          | some wire => (diagram.wires wire).sig == .rel args
          | none => false) &&
        (List.range args.length).all (fun index =>
          match diagram.endpointOwner? ⟨node, .arg index⟩, args[index]? with
          | some wire, some expected => (diagram.wires wire).sig == expected
          | _, _ => false)
    | _ => true) = true

/-- Ref positional arguments have the signatures stored on that ref. -/
def RefPortsTyped (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.nodesList.all (fun node =>
    match diagram.nodes node with
    | .ref _ _ args =>
        (List.range args.length).all (fun index =>
          match diagram.endpointOwner? ⟨node, .arg index⟩, args[index]? with
          | some wire, some expected => (diagram.wires wire).sig == expected
          | _, _ => false)
    | _ => true) = true

/-- Every identity node has at least two derived ports. -/
def IdentitiesHaveArity (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.nodesList.all (fun node =>
    match diagram.nodes node with
    | .identity _ _ arity => decide (2 ≤ arity)
    | _ => true) = true

/-- Every identity incidence has the one signature stored on its node. -/
def IdentityPortsTyped (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.nodesList.all (fun node =>
    match diagram.nodes node with
    | .identity _ sig arity =>
        (List.range arity).all (fun index =>
          match diagram.endpointOwner? ⟨node, .identity index⟩ with
          | some wire => (diagram.wires wire).sig == sig
          | none => false)
    | _ => true) = true

/-- A wire's lexical scope dominates the region of each incident node. -/
def WireScopesEnclose (diagram : ConcreteDiagram definitionCount) : Prop :=
  diagram.endpointOccurrences.all (fun occurrence =>
    decide (diagram.Encloses (diagram.wires occurrence.1).scope
      (diagram.nodes occurrence.2.node).region)) = true

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.RootIsSheet := by unfold RootIsSheet; infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.OnlyRootIsSheet := by unfold OnlyRootIsSheet; infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.AllRegionsReachRoot := by
  unfold AllRegionsReachRoot
  infer_instance

instance (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) :
    Decidable (diagram.ReferencesMatch definitions) := by
  unfold ReferencesMatch
  infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.PortsExist := by unfold PortsExist; infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.NoDuplicateEndpoints := by
  unfold NoDuplicateEndpoints
  infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.PortsCoveredExactlyOnce := by
  unfold PortsCoveredExactlyOnce
  infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.AtomPortsTyped := by unfold AtomPortsTyped; infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.RefPortsTyped := by unfold RefPortsTyped; infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.IdentitiesHaveArity := by
  unfold IdentitiesHaveArity
  infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.IdentityPortsTyped := by
  unfold IdentityPortsTyped
  infer_instance

instance (diagram : ConcreteDiagram definitionCount) :
    Decidable diagram.WireScopesEnclose := by
  unfold WireScopesEnclose
  infer_instance

/-- The one proof-level contract, assembled from independent graph invariants. -/
structure WellFormed (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) : Prop where
  root_is_sheet : diagram.RootIsSheet
  only_root_is_sheet : diagram.OnlyRootIsSheet
  all_regions_reach_root : diagram.AllRegionsReachRoot
  references_match : diagram.ReferencesMatch definitions
  ports_exist : diagram.PortsExist
  no_duplicate_endpoints : diagram.NoDuplicateEndpoints
  ports_covered_exactly_once : diagram.PortsCoveredExactlyOnce
  atom_ports_typed : diagram.AtomPortsTyped
  ref_ports_typed : diagram.RefPortsTyped
  identities_have_arity : diagram.IdentitiesHaveArity
  identity_ports_typed : diagram.IdentityPortsTyped
  wire_scopes_enclose : diagram.WireScopesEnclose

theorem endpointOwner?_occurs
    (diagram : ConcreteDiagram definitionCount)
    (endpoint : CEndpoint diagram.nodeCount) (wire : diagram.WireId)
    (owner : diagram.endpointOwner? endpoint = some wire) :
    (wire, endpoint) ∈ diagram.endpointOccurrences := by
  unfold ConcreteDiagram.endpointOwner? at owner
  cases found :
      diagram.endpointOccurrences.find? (fun occurrence =>
        occurrence.2 == endpoint) with
  | none => simp [found] at owner
  | some occurrence =>
      have occurrenceMember := List.mem_of_find?_eq_some found
      have endpointEquality : occurrence.2 = endpoint :=
        eq_of_beq (List.find?_some
          (p := fun occurrence :
            diagram.WireId × CEndpoint diagram.nodeCount =>
              occurrence.2 == endpoint) found)
      have wireEquality : occurrence.1 = wire := by
        simpa [found] using owner
      have pairEquality : occurrence = (wire, endpoint) :=
        Prod.ext wireEquality endpointEquality
      simpa [pairEquality] using occurrenceMember

theorem endpointOwner?_incident
    (diagram : ConcreteDiagram definitionCount)
    (endpoint : CEndpoint diagram.nodeCount) (wire : diagram.WireId)
    (owner : diagram.endpointOwner? endpoint = some wire) :
    endpoint ∈ (diagram.wires wire).endpoints := by
  have occurrence := endpointOwner?_occurs diagram endpoint wire owner
  simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap] at occurrence
  rcases occurrence with ⟨candidate, _, member⟩
  simp only [List.mem_map] at member
  rcases member with ⟨candidateEndpoint, candidateMember, equality⟩
  cases equality
  exact candidateMember

theorem endpointOwner?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (port : CPort)
    (required : port ∈ diagram.requiredPorts node) :
    ∃ wire, diagram.endpointOwner? ⟨node, port⟩ = some wire := by
  have nodeCheck := (List.all_eq_true.mp
    wellFormed.ports_covered_exactly_once) node
    (Data.Finite.mem_allFin node)
  have portCheck := (List.all_eq_true.mp nodeCheck) port required
  rw [Bool.and_eq_true] at portCheck
  exact Option.isSome_iff_exists.mp portCheck.2

theorem incident_port_required
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (wire : diagram.WireId)
    (endpoint : CEndpoint diagram.nodeCount)
    (incident : endpoint ∈ (diagram.wires wire).endpoints) :
    endpoint.port ∈ diagram.requiredPorts endpoint.node := by
  have occurrence :
      (wire, endpoint) ∈ diagram.endpointOccurrences := by
    simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
    refine ⟨wire, Data.Finite.mem_allFin wire, ?_⟩
    exact List.mem_map.mpr ⟨endpoint, incident, rfl⟩
  have checked := (List.all_eq_true.mp wellFormed.ports_exist)
    (wire, endpoint) occurrence
  exact of_decide_eq_true checked

private theorem eq_of_filter_length_one_of_mem
    {values : List α} {predicate : α → Bool} {left right : α}
    (leftMember : left ∈ values) (rightMember : right ∈ values)
    (leftAccepted : predicate left = true)
    (rightAccepted : predicate right = true)
    (one : (values.filter predicate).length = 1) :
    left = right := by
  have leftFiltered : left ∈ values.filter predicate := by
    exact List.mem_filter.mpr ⟨leftMember, leftAccepted⟩
  have rightFiltered : right ∈ values.filter predicate := by
    exact List.mem_filter.mpr ⟨rightMember, rightAccepted⟩
  cases filtered : values.filter predicate with
  | nil => simp [filtered] at leftFiltered
  | cons head tail =>
      rw [filtered] at one leftFiltered rightFiltered
      have tailEmpty : tail = [] := by
        have : tail.length = 0 := by simpa using one
        exact List.length_eq_zero_iff.mp this
      subst tail
      simp only [List.mem_cons, List.not_mem_nil, or_false] at leftFiltered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at rightFiltered
      exact leftFiltered.trans rightFiltered.symm

theorem endpointOwner?_eq_of_incident
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (port : CPort)
    (required : port ∈ diagram.requiredPorts node)
    (wire : diagram.WireId)
    (incident : (⟨node, port⟩ : CEndpoint diagram.nodeCount) ∈
      (diagram.wires wire).endpoints) :
    diagram.endpointOwner? ⟨node, port⟩ = some wire := by
  obtain ⟨owner, ownerEquation⟩ :=
    endpointOwner?_complete definitions diagram wellFormed node port required
  have ownerOccurrence :=
    endpointOwner?_occurs diagram ⟨node, port⟩ owner ownerEquation
  have wireOccurrence :
      (wire, (⟨node, port⟩ : CEndpoint diagram.nodeCount)) ∈
        diagram.endpointOccurrences := by
    simp only [ConcreteDiagram.endpointOccurrences, List.mem_flatMap]
    refine ⟨wire, Data.Finite.mem_allFin wire, ?_⟩
    exact List.mem_map.mpr ⟨⟨node, port⟩, incident, rfl⟩
  have nodeCheck := (List.all_eq_true.mp
    wellFormed.ports_covered_exactly_once) node
    (Data.Finite.mem_allFin node)
  have portCheck := (List.all_eq_true.mp nodeCheck) port required
  rw [Bool.and_eq_true] at portCheck
  have one : (diagram.endpointOccurrences.filter fun occurrence =>
      occurrence.2 == (⟨node, port⟩ :
        CEndpoint diagram.nodeCount)).length = 1 := by
    exact eq_of_beq portCheck.1
  have pairEquality :
      (owner, (⟨node, port⟩ : CEndpoint diagram.nodeCount)) =
        (wire, ⟨node, port⟩) := by
    apply eq_of_filter_length_one_of_mem
      (predicate := fun occurrence :
        diagram.WireId × CEndpoint diagram.nodeCount =>
          occurrence.2 == (⟨node, port⟩ :
            CEndpoint diagram.nodeCount))
      ownerOccurrence wireOccurrence
    · exact beq_self_eq_true _
    · exact beq_self_eq_true _
    · exact one
  have ownerEquality : owner = wire := congrArg Prod.fst pairEquality
  simpa [ownerEquality] using ownerEquation

private def secondSheetId (diagram : ConcreteDiagram definitionCount) : Nat :=
  match diagram.regionsList.find? (fun region =>
    decide (diagram.regions region = .sheet ∧ region ≠ diagram.root)) with
  | some region => region.val
  | none => diagram.root.val

private def unreachableRegionId (diagram : ConcreteDiagram definitionCount) : Nat :=
  match diagram.regionsList.find? (fun region =>
    !decide (diagram.Encloses diagram.root region)) with
  | some region => region.val
  | none => diagram.root.val

private def mismatchedReferenceId (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) : Nat :=
  match diagram.nodesList.find? (fun node =>
    match diagram.nodes node with
    | .ref _ definition args => args != definitions.get definition
    | _ => false) with
  | some node => node.val
  | none => 0

private def invalidEndpointData (diagram : ConcreteDiagram definitionCount) :
    Nat × Nat × CPort :=
  match diagram.endpointOccurrences.find? (fun occurrence =>
    !decide (occurrence.2.port ∈ diagram.requiredPorts occurrence.2.node)) with
  | some ⟨wire, endpoint⟩ => (wire.val, endpoint.node.val, endpoint.port)
  | none => (0, 0, .head)

private def duplicateEndpointData (diagram : ConcreteDiagram definitionCount) :
    Nat × Nat × CPort :=
  let rec first :
      List (diagram.WireId × CEndpoint diagram.nodeCount) →
      List (CEndpoint diagram.nodeCount) → Nat × Nat × CPort
    | [], _ => (0, 0, .head)
    | ⟨wire, endpoint⟩ :: tail, seen =>
        if endpoint ∈ seen then (wire.val, endpoint.node.val, endpoint.port)
        else first tail (endpoint :: seen)
  first diagram.endpointOccurrences []

private def coverageData (diagram : ConcreteDiagram definitionCount) :
    Nat × CPort :=
  let rec nodes : List diagram.NodeId → Nat × CPort
    | [] => (0, .head)
    | node :: tail =>
        match (diagram.requiredPorts node).find? (fun port =>
          diagram.endpointCount node port != 1) with
        | some port => (node.val, port)
        | none => nodes tail
  nodes diagram.nodesList

private def atomTypeData (diagram : ConcreteDiagram definitionCount) :
    Nat × CPort :=
  let rec nodes : List diagram.NodeId → Nat × CPort
    | [] => (0, .head)
    | node :: tail =>
        match diagram.nodes node with
        | .atom _ args =>
            match diagram.endpointOwner? ⟨node, .head⟩ with
            | some wire =>
                if (diagram.wires wire).sig != .rel args then (node.val, .head)
                else
                  match (List.range args.length).find? (fun index =>
                    match diagram.endpointOwner? ⟨node, .arg index⟩,
                        args[index]? with
                    | some owner, some expected =>
                        (diagram.wires owner).sig != expected
                    | _, _ => true) with
                  | some index => (node.val, .arg index)
                  | none => nodes tail
            | none => (node.val, .head)
        | _ => nodes tail
  nodes diagram.nodesList

private def refTypeData (diagram : ConcreteDiagram definitionCount) :
    Nat × CPort :=
  let rec nodes : List diagram.NodeId → Nat × CPort
    | [] => (0, .arg 0)
    | node :: tail =>
        match diagram.nodes node with
        | .ref _ _ args =>
            match (List.range args.length).find? (fun index =>
              match diagram.endpointOwner? ⟨node, .arg index⟩, args[index]? with
              | some owner, some expected =>
                  (diagram.wires owner).sig != expected
              | _, _ => true) with
            | some index => (node.val, .arg index)
            | none => nodes tail
        | _ => nodes tail
  nodes diagram.nodesList

private def arityNodeId (diagram : ConcreteDiagram definitionCount) : Nat :=
  match diagram.nodesList.find? (fun node =>
    match diagram.nodes node with
    | .identity _ _ arity => arity < 2
    | _ => false) with
  | some node => node.val
  | none => 0

private def identityTypeData (diagram : ConcreteDiagram definitionCount) :
    Nat × Nat :=
  let rec nodes : List diagram.NodeId → Nat × Nat
    | [] => (0, 0)
    | node :: tail =>
        match diagram.nodes node with
        | .identity _ sig arity =>
            match (List.range arity).find? (fun index =>
              match diagram.endpointOwner? ⟨node, .identity index⟩ with
              | some owner => (diagram.wires owner).sig != sig
              | none => true) with
            | some index => (node.val, index)
            | none => nodes tail
        | _ => nodes tail
  nodes diagram.nodesList

private def scopeData (diagram : ConcreteDiagram definitionCount) :
    Nat × Nat × CPort :=
  match diagram.endpointOccurrences.find? (fun occurrence =>
    !decide (diagram.Encloses (diagram.wires occurrence.1).scope
      (diagram.nodes occurrence.2.node).region)) with
  | some ⟨wire, endpoint⟩ => (wire.val, endpoint.node.val, endpoint.port)
  | none => (0, 0, .head)

end ConcreteDiagram

abbrev CheckedDiagram (definitions : List (List Sig)) :=
  { diagram : ConcreteDiagram definitions.length //
    diagram.WellFormed definitions }

structure OpenConcreteDiagram.WellFormed (definitions : List (List Sig))
    (openDiagram : OpenConcreteDiagram definitions.length) : Prop where
  diagram : openDiagram.diagram.WellFormed definitions
  boundary_root_scoped :
    openDiagram.boundary.all (fun wire =>
      decide ((openDiagram.diagram.wires wire).scope =
        openDiagram.diagram.root)) = true

abbrev CheckedOpenDiagram (definitions : List (List Sig)) :=
  { diagram : OpenConcreteDiagram definitions.length //
    diagram.WellFormed definitions }

namespace ConcreteDiagram

/-- The sole executable validation authority and its deterministic error order. -/
def checkWellFormed (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) :
    Except WFError (CheckedDiagram definitions) :=
  if hRoot : diagram.RootIsSheet then
    if hOnly : diagram.OnlyRootIsSheet then
      if hReach : diagram.AllRegionsReachRoot then
        if hRefs : diagram.ReferencesMatch definitions then
          if hExist : diagram.PortsExist then
            if hDup : diagram.NoDuplicateEndpoints then
              if hCover : diagram.PortsCoveredExactlyOnce then
                if hAtom : diagram.AtomPortsTyped then
                  if hRef : diagram.RefPortsTyped then
                    if hArity : diagram.IdentitiesHaveArity then
                      if hIdentity : diagram.IdentityPortsTyped then
                        if hScope : diagram.WireScopesEnclose then
                          .ok ⟨diagram,
                            ⟨hRoot, hOnly, hReach, hRefs, hExist, hDup,
                              hCover, hAtom, hRef, hArity, hIdentity,
                              hScope⟩⟩
                        else
                          let data := diagram.scopeData
                          .error (.wireScopeDoesNotEnclose
                            data.1 data.2.1 data.2.2)
                      else
                        let data := diagram.identityTypeData
                        .error (.identitySignatureMismatch data.1 data.2)
                    else
                      .error (.identityArityTooSmall diagram.arityNodeId)
                  else
                    let data := diagram.refTypeData
                    .error (.refSignatureMismatch data.1 data.2)
                else
                  let data := diagram.atomTypeData
                  .error (.atomSignatureMismatch data.1 data.2)
              else
                let data := diagram.coverageData
                .error (.missingOrDuplicatePort data.1 data.2)
            else
              let data := diagram.duplicateEndpointData
              .error (.duplicateEndpoint data.1 data.2.1 data.2.2)
          else
            let data := diagram.invalidEndpointData
            .error (.invalidEndpoint data.1 data.2.1 data.2.2)
        else
          .error (.referenceSignatureMismatch
            (diagram.mismatchedReferenceId definitions))
      else
        .error (.parentDoesNotReachRoot diagram.unreachableRegionId)
    else
      .error (.secondSheet diagram.secondSheetId)
  else
    .error .rootNotSheet

theorem checkWellFormed_preserves_input
    (ok : checkWellFormed definitions diagram = .ok checked) :
    checked.val = diagram := by
  unfold checkWellFormed at ok
  by_cases hRoot : diagram.RootIsSheet
  · rw [dif_pos hRoot] at ok
    by_cases hOnly : diagram.OnlyRootIsSheet
    · rw [dif_pos hOnly] at ok
      by_cases hReach : diagram.AllRegionsReachRoot
      · rw [dif_pos hReach] at ok
        by_cases hRefs : diagram.ReferencesMatch definitions
        · rw [dif_pos hRefs] at ok
          by_cases hExist : diagram.PortsExist
          · rw [dif_pos hExist] at ok
            by_cases hDup : diagram.NoDuplicateEndpoints
            · rw [dif_pos hDup] at ok
              by_cases hCover : diagram.PortsCoveredExactlyOnce
              · rw [dif_pos hCover] at ok
                by_cases hAtom : diagram.AtomPortsTyped
                · rw [dif_pos hAtom] at ok
                  by_cases hRef : diagram.RefPortsTyped
                  · rw [dif_pos hRef] at ok
                    by_cases hArity : diagram.IdentitiesHaveArity
                    · rw [dif_pos hArity] at ok
                      by_cases hIdentity : diagram.IdentityPortsTyped
                      · rw [dif_pos hIdentity] at ok
                        by_cases hScope : diagram.WireScopesEnclose
                        · rw [dif_pos hScope] at ok
                          cases ok
                          rfl
                        · rw [dif_neg hScope] at ok
                          cases ok
                      · rw [dif_neg hIdentity] at ok
                        cases ok
                    · rw [dif_neg hArity] at ok
                      cases ok
                  · rw [dif_neg hRef] at ok
                    cases ok
                · rw [dif_neg hAtom] at ok
                  cases ok
              · rw [dif_neg hCover] at ok
                cases ok
            · rw [dif_neg hDup] at ok
              cases ok
          · rw [dif_neg hExist] at ok
            cases ok
        · rw [dif_neg hRefs] at ok
          cases ok
      · rw [dif_neg hReach] at ok
        cases ok
    · rw [dif_neg hOnly] at ok
      cases ok
  · rw [dif_neg hRoot] at ok
    cases ok

theorem checkWellFormed_complete (wellFormed : diagram.WellFormed definitions) :
    checkWellFormed definitions diagram = .ok ⟨diagram, wellFormed⟩ := by
  rcases wellFormed with ⟨hRoot, hOnly, hReach, hRefs, hExist, hDup,
    hCover, hAtom, hRef, hArity, hIdentity, hScope⟩
  simp only [checkWellFormed, dif_pos hRoot, dif_pos hOnly, dif_pos hReach,
    dif_pos hRefs, dif_pos hExist, dif_pos hDup, dif_pos hCover,
    dif_pos hAtom, dif_pos hRef, dif_pos hArity, dif_pos hIdentity,
    dif_pos hScope]

theorem checkWellFormed_iff :
    (∃ checked,
      checkWellFormed definitions diagram = .ok checked ∧
      checked.val = diagram) ↔
      diagram.WellFormed definitions := by
  constructor
  · rintro ⟨checked, accepted, preserves⟩
    have property := checked.property
    rw [checkWellFormed_preserves_input accepted] at property
    exact property
  · intro wellFormed
    exact ⟨⟨diagram, wellFormed⟩,
      checkWellFormed_complete wellFormed, rfl⟩

instance wellFormedDecidable
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) :
    Decidable (diagram.WellFormed definitions) :=
  match accepted : checkWellFormed definitions diagram with
  | .ok checked => isTrue (by
      have property := checked.property
      rw [checkWellFormed_preserves_input accepted] at property
      exact property)
  | .error _ => isFalse fun wellFormed => by
      have complete := checkWellFormed_complete wellFormed
      rw [accepted] at complete
      contradiction

end ConcreteDiagram

export ConcreteDiagram (checkWellFormed)

end VisualProof
